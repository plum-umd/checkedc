int process_req1(char *msg |\textcolor{blue}{\encircle{\textbf{2}}} \faGears\usermods\textcolor{taintcolor}{\_Tainted}| , 
                 size_t m_l) 
                 |\textcolor{blue}{\encircle{\textbf{1}}} \usermods\textcolor{taintcolor}{\_Tainted}| {
 int rc = -1, i;
 if (m_l > MIN_SIZE) {
  msg += sscanf(msg, "%d", &i);
  if (i > 0) {
    char *cp1 |\textcolor{blue}{\encircle{\textbf{2}}} \faGears\usermods\textcolor{taintcolor}{\_Tainted}|;
    char *cp2 |\textcolor{blue}{\encircle{\textbf{2}}} \faGears\usermods\textcolor{taintcolor}{\_Tainted}|;
    char tmp[CMD_S] |\textcolor{blue}{\encircle{\textbf{2}}} \faGears\usermods\textcolor{taintcolor}{\_Tainted}|;
    for ( cp1 = msg, cp2 = tmp;
        *cp1 != '\0' && 
        cp2 - tmp < CMD_S - 1;
        ++cp1, ++cp2 )
    {
     switch ( *cp1 )
     {
       case '<':
        // We write 3 charecters into
        // cp2 but we ony checked for 1
        // charecter.
        *cp2++ = '&';
        |\realbug| *cp2++ = 'l';
        |\realbug| *cp2++ = 't';
        |\realbug| *cp2 = ';';
      break;
       ...
     } }
   ...
  } }
 return rc;
}
