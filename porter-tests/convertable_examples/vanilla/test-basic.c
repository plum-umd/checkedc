#include <stdio.h>

void print_arr1(int* arr, int len) {
	for (int i = 0; i < len; i++)
		printf("%d", arr[i]);
}

void print_arr2(int* arr, int len) {
	for (int i = 0; i < len; i++)
		printf("%d", *(arr + i));
}

int main(int argc, char const *argv[])
{
	int arr[5];

	for (int i = 0; i < 5; ++i) {
		arr[i] = i;
	}

	print_arr1(arr, 5);
	print_arr2(arr, 5);

	return 0;
}
