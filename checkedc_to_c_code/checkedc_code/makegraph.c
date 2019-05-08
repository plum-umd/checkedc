
#include <stdio_checked.h>
#include <stdchecked.h>
#include <stdlib_checked.h>

#pragma CHECKED_SCOPE ON

#define printf(...) unchecked { printf(__VA_ARGS__); }

static int remaining = 0;
static array_ptr<char> temp : count(remaining);
static array_ptr<void> localmalloc(int size) : byte_count(size);

struct hash_entry {
  unsigned int key;
  ptr<void> entry;
  ptr<struct hash_entry> next;
};

typedef ptr<struct hash_entry> HashEntry;

struct hash {
  array_ptr<HashEntry> array : count(size);
  int size;
};

typedef ptr<struct hash> Hash;
Hash MakeHash(int size);
int main(int argc, array_ptr<nt_array_ptr<char>> argv : count(argc));

int main(int argc, array_ptr<nt_array_ptr<char>> argv : count(argc)) {

  int size = 3;
  Hash my_hash = MakeHash(size);

  printf("my_hash: %p\n", my_hash);

  return 0;
}

Hash MakeHash(int size) {
  Hash retval = NULL;
  int i;

  retval = (Hash) localmalloc(sizeof(*retval));
  retval->array = (array_ptr<HashEntry>)localmalloc(size*sizeof(HashEntry));
  retval->size = size;
  for (i=0; i<size; i++)
    retval->array[i] = NULL;
  return retval;
}

static array_ptr<void> localmalloc(int size) : byte_count(size) {
  array_ptr<void> blah;
  
  if (size>remaining) 
    {
      temp = calloc<char>(32768, sizeof(char));
      if (!temp) printf("Error! malloc returns null\n");
      remaining = 32768;
    }
  blah = temp;
  temp += size;
  remaining -= size;
  return blah;
}


