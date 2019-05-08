
#include <stdio.h>
#include <stdlib.h>

static int remaining = 0;
static char* temp;
static void* localmalloc(int size);

struct hash_entry {
  unsigned int key;
  void* entry;
  struct hash_entry* next;
};

typedef struct hash_entry* HashEntry;

struct hash {
  HashEntry* array;
  int size;
};

typedef struct hash* Hash;
Hash MakeHash(int size);
int main(int argc, char** argv);

int main(int argc, char** argv) {

  int size = 3;
  Hash my_hash = MakeHash(size);

  printf("my_hash: %p\n", my_hash);

  return 0;
}

Hash MakeHash(int size) {
  Hash retval = NULL;
  int i;

  retval = (Hash) localmalloc(sizeof(*retval));
  retval->array = (HashEntry*)localmalloc(size*sizeof(HashEntry));
  retval->size = size;
  for (i=0; i<size; i++)
    retval->array[i] = NULL;
  return retval;
}

static void* localmalloc(int size) {
  void* blah;
  
  if (size>remaining) 
    {
      temp = calloc(32768, sizeof(char));
      if (!temp) printf("Error! malloc returns null\n");
      remaining = 32768;
    }
  blah = temp;
  temp += size;
  remaining -= size;
  return blah;
}


