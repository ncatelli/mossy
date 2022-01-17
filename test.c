int x;

long main() {
	int arr[3];
	int a, b, c;
	long y;
	int* testref;
	testref = &a;

	a = 1;
	b = 2;
	c = 3;
	x = 6;
	y = 7;
	y = 8;
	arr[0] = 9;
	return x + arr[0] + y;
}