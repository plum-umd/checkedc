|\entrypoint| // Entry point
void server_loop(int sock_fd) {
 ...
 |\textcolor{checkcolor}{\_Array\_ptr}|<struct queue> p : count(b_z) = NULL;
 ...
}

int process_req2(_Array_ptr<char> msg: count(m_l), 
                 size_t m_l) {
 ...
 char anum |\textcolor{checkcolor}{\_Checked}|[MAX_MSG_SIZE] = {0};
 ...
}