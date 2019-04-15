#include <stdio.h>
#define MAX 5

void print_arr(int* arr) {
	for (int i = 0; i < MAX; i++)
		printf("%d", *(arr + i));
}

int main(int argc, char const *argv[])
{
	int arr[8];

	for (int i = 0; i < 6; ++i) {
		arr[i] = i;
	}

	print_arr(arr);

	return 0;
}
