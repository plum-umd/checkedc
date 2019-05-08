#include <stdlib_checked.h>
#include <stdio_checked.h>
#include <stdchecked.h>

#pragma CHECKED_SCOPE ON

int main(int argc, _Array_ptr<_Nt_array_ptr<char>> argv : count(argc)) {
  int NumNodes = 1;
  int nbody = 0;

  if (argc > 2)
    NumNodes = atoi(argv[2]);
  else
    NumNodes = 4;

  if (argc > 1)
    nbody = atoi(argv[1]);
  else
    nbody = 32;

  unchecked {
    printf("%d\n", nbody);
  }
  
  return nbody;
}
