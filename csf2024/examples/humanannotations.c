size_t read_msg(int sock_fd, char *msg, 
                size_t sz) |\textcolor{taintcolor}{\_Tainted}| |\useradded| {
 ...
}

int process_req1(char *msg, size_t m_l) |\textcolor{taintcolor}{\_Tainted}| |\useradded| {
 ...
}
