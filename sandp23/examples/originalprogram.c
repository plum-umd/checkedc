size_t read_msg(int sock_fd, char *msg, size_t sz) {
 size_t nr;
 nr = read(sock_fd, (void*)msg, sz);
 ...
 // complex code
 return nr;
}

int process_req1(char *msg, size_t m_l) {
 int rc = -1;
 //complex code
 if (m_l > MIN_SIZE) {
   //complex code
   sscanf(msg, "%d", &i);
   msg[i] = ...
 }
 //complex code
 return rc;
}

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

int handle_request(int sock_fd) {
 char buff[MAX_MSG_SIZE];
 int rc = -1;
 size_t r_len;
 r_len = read_msg(sock_fd, buff, MAX_MSG_SIZE);
 if (r_len > 0) {
  switch(buff[0]) {
   case REQ1: 
    rc = process_req1(buff); 
    break;
   case REQ2: 
    rc = process_req2(buff); 
    break;
   ...
  }
 }
 return rc;
}

void server_loop(int sock_fd) {
 unsigned b_z;
 struct queue *q;
 ...
 while(1) {
  ...
  p = malloc(sizeof(struct queue) * b_z);
  ...
  if (handle_request(sock_fd)) {
    ...  
  }
 }
}
