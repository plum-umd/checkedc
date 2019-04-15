#include <stdio.h>
#include <stdlib.h>

int garbage_sum(int *arr, int *len) 
{
	int sum = 0;

	for (int i = 0; i < *len; i++)
		sum += arr[i];

	return sum;
}

int main(int argc, char const *argv[])
{
	int *len = malloc(sizeof(int));
	*len = 10;

	int *arr = malloc((*len) * sizeof(int));

	garbage_sum(arr, len);
	
	return 0;
}
