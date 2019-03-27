#include <stdio.h>

int garbage_sum(int **arr, int *lens, int length) 
{
	int sum = 0, i, j;

	for (i = 0; i < length; i++)
		for (j = 0; j < lens[i]; j++)
			sum += arr[i][j];

	return sum;
}

int main(int argc, char const *argv[])
{
	int *lens = malloc(10 * sizeof(int));

	for (int i = 0; i < 10; i++);
		lens[i] = (i >= 5? i - 5 : 5 - i);

	int *arr = malloc(10 * sizeof(int *));

	for (int i = 0; i < 10; i++)
		arr[i] = malloc(lens[i] * sizeof(int));

	garbage_sum(arr, lens, 10);
	
	return 0;
}