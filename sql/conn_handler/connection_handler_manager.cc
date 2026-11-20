/*
   Copyright (c) 2013, 2022, Oracle and/or its affiliates.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License, version 2.0,
   as published by the Free Software Foundation.

   This program is also distributed with certain software (including
   but not limited to OpenSSL) that is licensed under separate terms,
   as designated in a particular file or component or in included license
   documentation.  The authors of MySQL hereby grant you an additional
   permission to link the program and your derivative works with the
   separately licensed software that they have included with MySQL.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License, version 2.0, for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301  USA
*/

#include "sql/conn_handler/connection_handler_manager.h"

#include <assert.h>
#include <ctime>
#include <new>

#include "my_macros.h"
#include "my_psi_config.h"
#include "my_sys.h"
#include "mysql/components/services/bits/mysql_cond_bits.h"
#include "mysql/components/services/bits/mysql_mutex_bits.h"
#include "mysql/components/services/bits/psi_bits.h"
#include "mysql/components/services/bits/psi_cond_bits.h"
#include "mysql/components/services/bits/psi_mutex_bits.h"
#include "mysql/service_thd_wait.h"
#include "mysqld_error.h"                              // ER_*
#include "sql/conn_handler/channel_info.h"             // Channel_info
#include "sql/conn_handler/connection_handler_impl.h"  // Per_thread_connection_handler
#include "sql/conn_handler/plugin_connection_handler.h"  // Plugin_connection_handler
#include "sql/current_thd.h"
#include "sql/mysqld.h"        // max_connections
#include "sql/sql_callback.h"  // MYSQL_CALLBACK
#include "thr_lock.h"
#include "thr_mutex.h"

struct Connection_handler_functions;

// Initialize static members
uint Connection_handler_manager::connection_count = 0;
ulong Connection_handler_manager::max_used_connections = 0;
ulong Connection_handler_manager::max_used_connections_time = 0;
THD_event_functions *Connection_handler_manager::event_functions = nullptr;
THD_event_functions *Connection_handler_manager::saved_event_functions =
    nullptr;
mysql_mutex_t Connection_handler_manager::LOCK_connection_count;
mysql_cond_t Connection_handler_manager::COND_connection_count;
Connection_handler_manager *Connection_handler_manager::m_instance = nullptr;
// SNIPPET_START field_thread_handling
/*
 * 该变量用于决定使用何种连接处理器。
 * 这里的默认值意味着：每个连接都由一个专属的线程来处理。
 * 是指创建新连接的时候创建全新的线程吗？
 */
ulong Connection_handler_manager::thread_handling =
    SCHEDULER_ONE_THREAD_PER_CONNECTION;
// SNIPPET_END field_thread_handling
uint Connection_handler_manager::max_threads = 0;

/**
  Helper functions to allow mysys to call the thread scheduler when
  waiting for locks.
*/

static void scheduler_wait_lock_begin() {
  MYSQL_CALLBACK(Connection_handler_manager::event_functions, thd_wait_begin,
                 (current_thd, THD_WAIT_TABLE_LOCK));
}

static void scheduler_wait_lock_end() {
  MYSQL_CALLBACK(Connection_handler_manager::event_functions, thd_wait_end,
                 (current_thd));
}

static void scheduler_wait_sync_begin() {
  MYSQL_CALLBACK(Connection_handler_manager::event_functions, thd_wait_begin,
                 (current_thd, THD_WAIT_SYNC));
}

static void scheduler_wait_sync_end() {
  MYSQL_CALLBACK(Connection_handler_manager::event_functions, thd_wait_end,
                 (current_thd));
}

bool Connection_handler_manager::valid_connection_count() {
  bool connection_accepted = true;
  mysql_mutex_lock(&LOCK_connection_count);
  if (connection_count > max_connections) {
    connection_accepted = false;
    m_connection_errors_max_connection++;
  }
  mysql_mutex_unlock(&LOCK_connection_count);
  return connection_accepted;
}

// SNIPPET_START check_and_incr_conn_count
bool Connection_handler_manager::check_and_incr_conn_count(
    bool is_admin_connection) {
  bool connection_accepted = true;
  mysql_mutex_lock(&LOCK_connection_count);
  // SNIPPET_IGNORE_START
  /*
    Here we allow max_connections + 1 clients to connect
    (by checking before we increment by 1).

    The last connection is reserved for SUPER users. This is
    checked later during authentication where valid_connection_count()
    is called for non-SUPER users only.
  */
  // SNIPPET_IGNORE_END
  if (connection_count > max_connections && !is_admin_connection) {
    connection_accepted = false;
    // 连接错误计数增1
    m_connection_errors_max_connection++;
  } else { // 如果连接数没有超过最大值，或者是admin连接
    // 连接数增1
    ++connection_count;

    // 如果连接数超了，那说明当前请求只能是admin请求了
    if (connection_count > max_used_connections) {
      // 更新一下最大连接数，因为admin连接是不会占用普通连接的名额的。
      max_used_connections = connection_count;
      // 重置一下达到最大连接数的时间
      max_used_connections_time = time(nullptr);
    }
  }
  mysql_mutex_unlock(&LOCK_connection_count);
  return connection_accepted;
}
// SNIPPET_END check_and_incr_conn_count

#ifdef HAVE_PSI_INTERFACE
static PSI_mutex_key key_LOCK_connection_count;

static PSI_mutex_info all_conn_manager_mutexes[] = {
    {&key_LOCK_connection_count, "LOCK_connection_count", PSI_FLAG_SINGLETON, 0,
     PSI_DOCUMENT_ME}};

static PSI_cond_key key_COND_connection_count;

static PSI_cond_info all_conn_manager_conds[] = {
    {&key_COND_connection_count, "COND_connection_count", PSI_FLAG_SINGLETON, 0,
     PSI_DOCUMENT_ME}};
#endif

// SNIPPET_START init_func
bool Connection_handler_manager::init() {
  /*
    This is a static member function.
    Per_thread_connection_handler's static members need to be initialized
    even if One_thread_connection_handler is used instead.
  */
  // 初始化默认类型处理器
  Per_thread_connection_handler::init();

  /*
   * 创建连接处理器
   */
  Connection_handler *connection_handler = nullptr;
  /*
   * 这里的thread_handling在上面有赋值，
   * 另外可以通过在MySQL客户端执行 SHOW VARIABLES LIKE "thread_handling" 来查询。
   */
  switch (Connection_handler_manager::thread_handling) {
    case SCHEDULER_ONE_THREAD_PER_CONNECTION: // 默认是这个
      // 不启用线程池，每一个连接用单独的线程处理
      connection_handler = new (std::nothrow) Per_thread_connection_handler();
      break;
    case SCHEDULER_NO_THREADS:
      // 启用线程池，所有连接用同一个线程处理
      connection_handler = new (std::nothrow) One_thread_connection_handler();
      break;
    default:
      assert(false);
  }

  if (connection_handler == nullptr) {
    // This is a static member function.
    Per_thread_connection_handler::destroy();
    return true;
  }

  /*
   * 创建连接处理器管理器对象，该对象是单例的。
   * 该类构造函数是private的，这里在静态函数init中创建对象，是单例模式的体现。
   */
  m_instance =
      new (std::nothrow) Connection_handler_manager(connection_handler);

  if (m_instance == nullptr) {
    delete connection_handler;
    // This is a static member function.
    Per_thread_connection_handler::destroy();
    return true;
  }

  // SNIPPET_IGNORE_START
#ifdef HAVE_PSI_INTERFACE
  int count = static_cast<int>(array_elements(all_conn_manager_mutexes));
  mysql_mutex_register("sql", all_conn_manager_mutexes, count);

  count = static_cast<int>(array_elements(all_conn_manager_conds));
  mysql_cond_register("sql", all_conn_manager_conds, count);
#endif

  mysql_mutex_init(key_LOCK_connection_count, &LOCK_connection_count,
                   MY_MUTEX_INIT_FAST);

  mysql_cond_init(key_COND_connection_count, &COND_connection_count);

  max_threads = connection_handler->get_max_threads();

  // Init common callback functions.
  thr_set_lock_wait_callback(scheduler_wait_lock_begin,
                             scheduler_wait_lock_end);
  thr_set_sync_wait_callback(scheduler_wait_sync_begin,
                             scheduler_wait_sync_end);
  // SNIPPET_IGNORE_END
  return false;
}
// SNIPPET_END init_func

void Connection_handler_manager::wait_till_no_connection() {
  mysql_mutex_lock(&LOCK_connection_count);
  while (connection_count > 0) {
    mysql_cond_wait(&COND_connection_count, &LOCK_connection_count);
  }
  mysql_mutex_unlock(&LOCK_connection_count);
}

void Connection_handler_manager::destroy_instance() {
  Per_thread_connection_handler::destroy();

  if (m_instance != nullptr) {
    delete m_instance;
    m_instance = nullptr;
    mysql_mutex_destroy(&LOCK_connection_count);
    mysql_cond_destroy(&COND_connection_count);
  }
}

void Connection_handler_manager::reset_max_used_connections() {
  mysql_mutex_lock(&LOCK_connection_count);
  max_used_connections = connection_count;
  max_used_connections_time = time(nullptr);
  mysql_mutex_unlock(&LOCK_connection_count);
}

void Connection_handler_manager::load_connection_handler(
    Connection_handler *conn_handler) {
  // We don't support loading more than one dynamic connection handler
  assert(Connection_handler_manager::thread_handling != SCHEDULER_TYPES_COUNT);
  m_saved_connection_handler = m_connection_handler;
  m_saved_thread_handling = Connection_handler_manager::thread_handling;
  m_connection_handler = conn_handler;
  Connection_handler_manager::thread_handling = SCHEDULER_TYPES_COUNT;
  max_threads = m_connection_handler->get_max_threads();
}

bool Connection_handler_manager::unload_connection_handler() {
  assert(m_saved_connection_handler != nullptr);
  if (m_saved_connection_handler == nullptr) return true;
  delete m_connection_handler;
  m_connection_handler = m_saved_connection_handler;
  Connection_handler_manager::thread_handling = m_saved_thread_handling;
  m_saved_connection_handler = nullptr;
  m_saved_thread_handling = 0;
  max_threads = m_connection_handler->get_max_threads();
  return false;
}

// SNIPPET_START process_new_connection
void Connection_handler_manager::process_new_connection(
    Channel_info *channel_info) {
  if (connection_events_loop_aborted() ||
      // 增加连接计数，如果超过了最大连接数，则发送错误码。
      !check_and_incr_conn_count(channel_info->is_admin_connection())) {
    // 客户端收到的1040错误码，就是这里的ER_CON_COUNT_ERROR
    channel_info->send_error_and_close_channel(ER_CON_COUNT_ERROR, 0, true);
    delete channel_info;
    return;
  }

  // 通过连接处理器添加连接
  if (m_connection_handler->add_connection(channel_info)) {
    inc_aborted_connects();
    delete channel_info;
  }
}
// SNIPPET_END process_new_connection

THD *create_thd(Channel_info *channel_info) {
  THD *thd = channel_info->create_thd();
  if (thd == nullptr)
    channel_info->send_error_and_close_channel(ER_OUT_OF_RESOURCES, 0, false);

  return thd;
}

void destroy_channel_info(Channel_info *channel_info) { delete channel_info; }

void dec_connection_count() {
  Connection_handler_manager::dec_connection_count();
}

void increment_aborted_connects() {
  Connection_handler_manager::get_instance()->inc_aborted_connects();
}

int my_connection_handler_set(Connection_handler_functions *chf,
                              THD_event_functions *tef) {
  assert(chf != nullptr && tef != nullptr);
  if (chf == nullptr || tef == nullptr) return 1;

  // 创建连接处理器
  Plugin_connection_handler *conn_handler =
      new (std::nothrow) Plugin_connection_handler(chf);
  if (conn_handler == nullptr) return 1;

  // 设置连接处理器
  Connection_handler_manager::get_instance()->load_connection_handler(
      conn_handler);
  Connection_handler_manager::saved_event_functions =
      Connection_handler_manager::event_functions;
  Connection_handler_manager::event_functions = tef;
  return 0;
}

int my_connection_handler_reset() {
  Connection_handler_manager::event_functions =
      Connection_handler_manager::saved_event_functions;
  return Connection_handler_manager::get_instance()
      ->unload_connection_handler();
}
