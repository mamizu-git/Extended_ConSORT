#include "seahorn/seahorn.h"
#define N 1000

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

int main() {
  int i;
  int* p = a;
  init_i(N, a);

  for(i = 0; i < 3; i++)
    sassert(a[i] == i);

  return 42;
}