#include <stdio.h>

void make_array(int len) {
	int arr[len];

	for (int i = 0; i < len; ++i) {
		arr[i] = i;
	}
}

int main(int argc, char const *argv[])
{
	for (int i = 0; i < 100; ++i) {
		make_array(i);
	}


	return 0;
}
