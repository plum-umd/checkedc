#include <stdio_checked.h>
#include <stdlib_checked.h>
#include <stdchecked.h>

#pragma CHECKED_SCOPE ON

int garbage_sum(array_ptr<int> arr : count(*len), ptr<int> len) 
{
	int sum = 0;

	for (int i = 0; i < *len; i++)
		sum += arr[i];

	return sum;
}

/*int main(int argc, nt_array_ptr<char> argv checked[] : count(argc))
{
	int len = 10;

	array_ptr<int> arr : count(len) = malloc<int>(len * sizeof(int));

	garbage_sum(arr, &len);
	
	return 0;
}*/