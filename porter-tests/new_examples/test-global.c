#include <stdio.h>

int max = 5;

void print_arr(int* arr) {
	for (int i = 0; i < max; i++)
		printf("%d", *(arr + i));
}

int main(int argc, char const *argv[])
{
	int arr[50];

	for (int i = 0; i < 50; ++i) {
		arr[i] = i;
	}

	print_arr(arr);

	return 0;
}
