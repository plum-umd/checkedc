size_t read_msg(int sock_fd, char *msg, 
                size_t sz) |\textcolor{taintcolor}{\_\_tainted}| |\useradded| {
 ...
}

int process_req1(char *msg, size_t m_l) |\textcolor{taintcolor}{\_\_tainted}| |\useradded| {
 ...
}
