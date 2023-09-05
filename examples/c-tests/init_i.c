#include "seahorn/seahorn.h"
#define N 10

int a[N];

extern int unknown1(void);

void init_i(int n, int* p);

void init_i(int n, int* p) {
  if (n <= 0) {

  } else {
    if (n == 1) {
      *p = 0;
    } else {
      int* q = p + (n-1);
      *q = (n-1);
      init_i(n-1, p);
    }
  }
}

int my_abs_min(int x, int n);

int my_abs_min(int x, int n) {
  if (x >= 0) {
    if (n > x) {
      return x;
    } else {
      return n;
    }
  } else {
    if (n > -x) {
      return -x;
    } else {
      return n;
    }
  }
}

int main() {
  int i;
  int* p = a;
  init_i(N, a);

  for(i = 0; i < N; i++)
    sassert(a[i] == i);

  int j = my_abs_min(unknown1 (), N-1);
  sassert(a[j] + a[N-1-j] == N-1);

  return 42;
}