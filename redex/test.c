#include <stdio_checked.h> 
#include <stdlib.h> 
#include <stdchecked.h> 
#include <string_checked.h> 

typedef struct _g7008 {
ptr<int> g7009;
ptr<int> g7010;
int g7011;
int g7012;
array_ptr<int> g7013;
ptr<int> g7014;
ptr<int> g7015;
int g7016;
int g7017;
int g7018;
} g7008;
array_ptr<int> fun(void) : count(6);

array_ptr<int> fun(void) : count(6) {
  array_ptr<int> p : count(6) =  calloc<int>(6, sizeof(int));
  *p = 5;
  p++;
  return p;
}

int main(void) _Checked {
  int x = 5;
  //ptr<int> p = calloc<int>(x, sizeof(int));
  return x;
}
