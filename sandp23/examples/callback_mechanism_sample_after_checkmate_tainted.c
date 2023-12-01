// CheckMate inserts headers

char * StringProc(const char * string,
char * (*StringAuth)(const char * input,size_t len)) {
  ...
  //Complex code definition converted to generic-C
  ...
  strncpy(local_str, user_input[i], len); //CheckMate modified 
  ...
  return StringAuth(one_past_start, string_len);
}

int isStringMatching(char* str1 ,
                char* str2)
{
  ...
  //complex Function body
  ...
}

