|\entrypoint| // Entry point
void server_loop(int sock_fd) {
 unsigned b_z;
 struct queue *p;
 ...
 while(1) {
  ...
  p = malloc(sizeof(struct queue) * b_z);
  ...
  if (handle_request(sock_fd)) {...}
 }
}

int handle_request(int sock_fd) {
 char buff[MAX_MSG_SIZE] |\textcolor{blue}{\encircle{\textbf{3}}} \faGears\usermods\textcolor{taintcolor}{\_Tainted}|;
 int rc = -1;
 ssize_t r_len;
 r_len = read(sock_fd, buff, 
              MAX_MSG_SIZE);
 if (r_len > 0 && 
     r_len < MAX_MSG_SIZE) {
  switch(buff[0]) {
   case REQ1: 
    rc = process_req1(buff, r_len); 
    break;
   case REQ2:
   ...
  }
 }
 return rc;
}
