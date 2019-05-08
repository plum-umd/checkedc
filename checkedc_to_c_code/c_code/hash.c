
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char** argv);
static void* localmalloc(int size);

static int remaining = 0;
static char* temp;

int main(int argc, char** argv) {

  localmalloc(20);

  return 0;
}

static void* localmalloc(int size) {
  void* blah;
  
  if (size > remaining) {
      temp = calloc(32768, sizeof(char));
      if (!temp) printf("Error! malloc returns null\n");
      remaining = 32768;
    }
  blah = temp;
  temp += size;
  remaining -= size;
  
  return blah;
}

