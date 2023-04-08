#include <string_tainted.h>

_Callback _TPtr<char> StringAuth(_TPtr<const char> input , size_t len) {
   ...
   //complex Function Body
   ...
}

/*
 * CheckMate Inserted Callback Registration
 */

void registerCallback_StringAuth(void){
    //callback function signature {ret <- int, arg_1 <- int, arg_2 <- long}
    int ret_param_types[] = {0, 0, 1}; 
    // 2 <- arg count, 1 <- ret count 
    __StringAuth__C_ = _SBXREG_((void*)_T_StringAuth,2,1, ret_param_types);
}

/*
 * CheckMate Inserted Trampoline for Directing Callbacks from WASM sandbox
 */

unsigned int _T_StringAuth(unsigned sandbox,
                                 unsigned int arg_1,
                                 unsigned long int arg_2) {
    return StringAuth(arg_1, (size_t)arg_2);
}

_Tainted _TPtr<char> StringProc(_TPtr<_TPtr<const char>> string,
_TPtr<_TPtr<char>(_TPtr<const char> input, size_t len)>StringAuth) {
	
   // StringAuth as a function ptr arg is only used as a 
   //_Callback signature to CheckMate and for type-checker
   return w2c_StringProc(_SBX_(), (unsigned int)string, __StringAuth__C_);
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

