#include "seahorn/seahorn.h"
#define N 3

int a[N];

extern int unknown1(void);

void init2(int n, int* p);

void init2(int n, int* p) {
  if (n <= 0) {

  } else {
    *p = 0;
    if (n == 1) {

    } else {
      int* q = p - 1;
      init2(n-1, q);
    }
  }
}

int main() {
  int i;

  int* p = a;

  int* b = a + (N-1);

  init2(N, b);

  for(i=0; i < N; i++)
    sassert(a[i] == 0);

  return 42;
}