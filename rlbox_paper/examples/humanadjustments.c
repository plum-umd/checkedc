int handle_request(int sock_fd) {
 char buff[MAX_MSG_SIZE] |\textcolor{taintcolor}{\_\_tainted} \usermods|;
 ...
}

int process_req2(|\usermods| |\textcolor{taintcolor}{\_t\_Array\_ptr}|<char> msg: count(m_l), 
                 size_t m_l) {
 ...
}
