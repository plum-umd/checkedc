#include <stdio.h>

int main(int argc, char const *argv[])
{
	int len;

	scanf("%d", &len);

	int arr[len];

	for (int i = 0; i < len; i++) {
		arr[i] = i;
	}

	return 0;
}