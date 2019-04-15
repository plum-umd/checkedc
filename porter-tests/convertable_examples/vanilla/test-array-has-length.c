#include <stdio.h>

void print_arr(int* arr) 
{
	for (int i = 0; i < arr[0]; i++)
		printf("%d\t", arr[i]);
}

int main(int argc, char const *argv[])
{
	int arr[] = {8, 1, 2, 3, 7, 7, 7, 7};

	print_arr(arr);

	return 0;
}
