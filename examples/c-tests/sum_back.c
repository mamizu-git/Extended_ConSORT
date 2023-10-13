#include "seahorn/seahorn.h"
#define N 1000

int a[N];

extern int unknown1(void);

int my_abs(int x);

int my_abs(int x) {
  if (x >= 0) {
    return x;
  } else {
    return -x;
  }
}

int sum(int n, int* p);

int sum(int n, int* p) {
  if (n <= 0) {
    return 0;
  } else {
    if (n == 1) {
      return *p;
    } else {
      int* q = p + (n-1);
      int x = *q;
      int s = sum(n-1, p);
      return x + s;
    }
  }
}

int main() {
  int i;
  int j = my_abs(unknown1 ());

  for (i = 0; i < N; i++)
    a[i] = j;

  int* p = a;

  int s = sum(N, p);

  sassert(s >= 0);

  return 42;
}