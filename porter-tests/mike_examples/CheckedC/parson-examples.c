#include <stdlib_checked.h>
#include <string_checked.h>

#pragma CHECKED_SCOPE ON

struct value_t {
  int x;
  int y;
};

typedef struct value_t Value;

struct array_t {
  _Ptr<Value>  wrapping_value; // pointer to single value
  _Array_ptr<_Ptr<Value>> items : count(count) ; // array of pointers to single values; field capacity has size of array
  size_t       count; // invariant: count <= capacity
  size_t       capacity;
};

typedef struct array_t  Array;

#define STARTING_CAPACITY 16
#define MAX(a, b)             ((a) > (b) ? (a) : (b))

int array_resize(_Ptr<Array> array, size_t new_capacity) {
  if (new_capacity == 0 || new_capacity < array-> count) {
    return -1;
  }
  
  _Array_ptr<_Ptr<Value>> new_items : byte_count(new_capacity * sizeof(_Ptr<Value>)) =
    (_Array_ptr<_Ptr<Value>>)malloc<_Ptr<Value>>(new_capacity * sizeof(_Ptr<Value>));
  if (new_items == NULL) {
    return -1;
  }

  if (array->items != NULL && array->count > 0) {
    // These casts are making the pointer sizes smaller than their actual sizes;
    //   subtyping should do this for us
    memcpy<_Ptr<Value>>(_Dynamic_bounds_cast<_Array_ptr<_Ptr<Value>>>(new_items, byte_count(array->count * sizeof(_Ptr<Value>))),
			_Dynamic_bounds_cast<_Array_ptr<_Ptr<Value>>>(array->items, byte_count(array->count * sizeof(_Ptr<Value>))), 
			array->count * sizeof(_Ptr<Value>));
  }
  free<_Ptr<Value>>(array->items);
  array->capacity = new_capacity;
  // Compiler ought to be able to prove this, so unnecessary bounds check
  array->items = _Dynamic_bounds_cast<_Array_ptr<_Ptr<Value>>>(new_items, count(array->capacity));
  return 0;
}

int array_add(_Ptr<Array> array, _Ptr<Value> value) {
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

_Ptr<Value> array_get_value(const _Ptr<Array> array, size_t index) {
  if (array == NULL || index >= array->count) {
    return NULL;
  }
  return array->items[index];
}
