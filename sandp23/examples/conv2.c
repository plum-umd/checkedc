size_t read_msg(int sock_fd, char *msg, 
                size_t sz) _Tainted {
 size_t nr;
 nr = read(sock_fd, (void*)msg, sz);
 ...
 |\complexcode| // complex code
 return nr;
}

int process_req1(char *msg, size_t m_l) 
                 _Tainted {
 int rc = -1, i;
 if (m_l > MIN_SIZE) {
   sscanf(msg, "%d", &i);
   msg[i] = ...
 }
 // complex code
 return rc;
}

int process_req2(|\textcolor{taintcolor}{\_t\_Array\_ptr}|<char> msg : 
                 count(m_l), 
                 size_t m_l) {
 size_t i = 0, j = 0;
 int rc = -1;
 char anum |\textcolor{checkcolor}{\_Checked}|[MAX_MSG_SIZE] = {0};
 if (msg) {
  while(i < m_l && j < MAX_MSG_SIZE-1) {
   ...
   if (isalnum(msg[i]))
    anum[j++] = msg[i]; 
   i++;
  }
   rc = process_data(anum);
 }
 return rc;
}
