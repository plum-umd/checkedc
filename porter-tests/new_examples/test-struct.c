#include <stdio.h>
#include <stdlib.h>

struct example {
	int* arr;
};

void print_arr(struct example obj, int len) {
	for (int i = 0; i < len; i++)
		printf("%d", *(obj.arr + i));
}

int main(int argc, char const *argv[])
{
	struct example obj;
	int len = 20;
	obj.arr = malloc(len * sizeof(int));

	for (int i = 0; i < len; ++i) {
		obj.arr[i] = i;
	}

	print_arr(obj, len);

	return 0;
}
