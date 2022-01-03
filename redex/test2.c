#include <stdio_checked.h> 
#include <stdlib.h> 
#include <stdchecked.h> 
#include <string_checked.h> 
array_ptr<int> f(void ) : count(5) {
  array_ptr<int> x : count(5) = calloc<int>( 5, sizeof(int)); 
return x;
}
array_ptr<int> g(void ) : count(5) {
 array_ptr<int> x : count(5) = calloc<int>( 5, sizeof(int)); 
return x+3;
}
int main(void) _Checked {
 return ( 0 ? g( ) : f( )+3 );
}
