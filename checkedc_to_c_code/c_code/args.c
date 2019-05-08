
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char** argv) {
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

  printf("%d\n", nbody);
  
  return nbody;
}
