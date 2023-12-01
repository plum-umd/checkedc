#include <string_tainted.h> //tainted wrapper of STDLIB string.h
...

_Callback _TPtr<char> StringAuth(_TPtr<const char> input , size_t len) {
  ...
  //complex Function Body
  /*
  "_Callback" allows access to global checked data
  
  "_Callback" restricts function signature to
  only contain pointers of Tainted type
  Since Callbacks execute in checked region, they have no 
  restrictions on callees.
  */
  ...
}

_Tainted _TPtr<char> StringProc(_TPtr<_TPtr<const char>> user_input,
_TPtr<_TPtr<char>(_TPtr<const char> input, size_t len)>StringAuth) {
  ...
  //complex Function Body	
  
   /*
   "_Tainted" restricts access to global data 
   
   "_Tainted" restricts function signature to 
   only contain pointers of Tainted type 
  
   Since "_Tainted" functions are destined to execute in unchecked
   region, callees of this function must be "_Mirror", "_Callback" or 
   "_Tainted" qualified. 
  */
  ...
  t_strncpy(local_str, user_input[i], len); // tainted wrapper for strncpy
  ...
  return StringAuth(one_past_start, string_len);
}

_Mirror int isStringMatching(char* str1 : itype (_Ptr<char>), 
		char* str2 : itype(_Ptr<char>))
{
  ...
  //complex Function body
  /*
   * "_Mirror" restricts access to global data
   * 
   * Since "_Mirror" functions are locally replicated in both 
   * checked and unchecked regions, they have no restriction on 
   * type signature and callees.
   */
  ...
}
