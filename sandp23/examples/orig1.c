|\entrypoint| // Entry point
void server_loop(int sock_fd) {
 unsigned b_z;
 struct queue *p;
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

int handle_request(int sock_fd) {
 char buff[MAX_MSG_SIZE];
 int rc = -1;
 size_t r_len;
 r_len = read_msg(sock_fd, buff, 
                  MAX_MSG_SIZE);
 if (r_len > 0) {
  switch(buff[0]) {
   case REQ1: 
    rc = process_req1(buff, r_len); 
    break;
   case REQ2: 
    rc = process_req2(buff, r_len); 
    break;
   ...
  }
 }
 return rc;
}
