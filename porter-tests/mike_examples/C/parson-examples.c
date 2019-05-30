#include <stdlib.h>
#include <string.h>

struct value_t {
  int x;
  int y;
};

typedef struct value_t Value;

struct array_t {
  Value  *wrapping_value; // pointer to single value
  Value **items; // array of pointers to single values; field capacity has size of array
  size_t       count; // invariant: count <= capacity
  size_t       capacity;
};

typedef struct array_t  Array;

#define STARTING_CAPACITY 16
#define MAX(a, b)             ((a) > (b) ? (a) : (b))

int array_resize(Array *array, size_t new_capacity) {
  if (new_capacity == 0 || new_capacity < array-> count) {
    return -1;
  }
  Value **new_items = malloc(new_capacity * sizeof(Value *));
  if (new_items == NULL) {
    return -1;
  }

  if (array->items != NULL && array->count > 0) {
    memcpy(new_items, array->items, array->count * sizeof(Value*));
  }
  free(array->items);
  array->capacity = new_capacity; 
  array->items = new_items;
  return 0;
}

int array_add(Array *array, Value *value) {
  if (array->count >= array->capacity) {
    size_t new_capacity = MAX(array->capacity * 2, STARTING_CAPACITY);
    if (array_resize(array, new_capacity) == -1) {
      return -1;
    }
  }
  array->items[array->count] = value;
  array->count++;
  return 0;
}

Value * array_get_value(const Array *array, size_t index) {
  if (array == NULL || index >= array->count) {
    return NULL;
  }
  return array->items[index];
}
