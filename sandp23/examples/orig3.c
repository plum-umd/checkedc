int process_req2(char *msg, size_t m_l) {
 size_t i = 0, j = 0;
 int rc = -1;
 char anum[MAX_MSG_SIZE] = {0};
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
