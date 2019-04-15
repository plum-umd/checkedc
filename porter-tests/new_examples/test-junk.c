#include <stdio.h>

void print_arr(int* arr, int y, int low, int high, char c, int* x) {
	*x = y + (int) c;
	for (int i = 0; i < high; i++)
		printf("%d", *(arr + low + i));
	c = (char) y;
	y++;
}

int main(int argc, char const *argv[])
{
	int[] arr = new arr[50];
	int x = 2;

	for (int i = 0; i < 50; ++i) {
		arr[i] = i;
	}

	print_arr(arr, 5, 20, 30, 'a', &x);

	return 0;
}