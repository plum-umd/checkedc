
#include <stdchecked.h>
#include <stdlib_checked.h>
#include <stdio_checked.h>

#pragma CHECKED_SCOPE ON

#define printf(...) unchecked { printf(__VA_ARGS__); }

int main(int argc, _Array_ptr<_Nt_array_ptr<char>> argv : count(argc));
static array_ptr<void> localmalloc(int size) : byte_count(size);

static int remaining = 0;
static array_ptr<char> temp : count(remaining);


int main(int argc, _Array_ptr<_Nt_array_ptr<char>> argv : count(argc)) {

  localmalloc(20);

  return 0;
}

static array_ptr<void> localmalloc(int size) : byte_count(size) {
  array_ptr<void> blah;
  
  if (size>remaining) {
      temp = calloc<char>(32768, sizeof(char));
      if (!temp) printf("Error! malloc returns null\n");
      remaining = 32768;
    }
  blah = temp;
  temp += size;
  remaining -= size;
  
  return blah;
}
