#include "seahorn/seahorn.h"
#define N 1000

int a[N];

extern int unknown1(void);

void init(int n, int* p);

void init(int n, int* p) {
  if (n <= 0) {

  } else {
    *p = 0;
    if (n == 1) {

    } else {
      int* q = p + 1;
      init(n-1, q);
    }
  }
}

int main() {
  int i;

  int* p = a;

  init(N, a);

  for(i=0; i < 3; i++)
    sassert(a[i] == 0);

  return 42;
}