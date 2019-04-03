#include <stdio.h>

struct len
{
	int length;
};

void print_arr(int* arr, struct len* ls) 
{
	for (int i = 0; i < ls->length; i++)
		printf("%d\t", arr[i]);
}

int main(int argc, char const *argv[])
{
	int[] arr = {8, 1, 2, 3, 7, 7, 7, 7};
	struct len ls;
	ls.length = 8; 

	print_arr(arr, &ls);

	return 0;
}