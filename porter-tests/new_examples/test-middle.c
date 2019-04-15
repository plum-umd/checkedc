#include <stdio.h>

void print_arr(int* arr, int low, int high) {
	for (int i = 0; i < high; i++)
		printf("%d", *(arr + low + i));
}

int main(int argc, char const *argv[])
{
	int[] arr = new arr[50];

	for (int i = 0; i < 50; ++i) {
		arr[i] = i;
	}

	print_arr(arr, 20, 30);

	return 0;
}