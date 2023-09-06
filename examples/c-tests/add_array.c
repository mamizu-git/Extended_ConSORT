#include "seahorn/seahorn.h"
#define N 1000

int a[N];
int b[N];
int c[N];

extern int unknown1(void);

int my_abs(int x);

int my_abs(int x) {
  if (x >= 0) {
    return x;
  } else {
    return -x;
  }
}

void add(int n, int* p, int* q, int* r);

void add(int n, int* p, int* q, int* r) {
  if (n <= 0) {

  } else {
    if (n == 1) {
      *r = *p + *q;
    } else {
      *r = *p + *q;
      int* p1 = p + 1;
      int* q1 = q + 1;
      int* r1 = r + 1;
      add(n-1, p1, q1, r1);
    }
  }
}

int main() {
  int i;
  int j = my_abs(unknown1 ());

  for (i = 0; i < N; i++) {
    a[i] = j;
    b[i] = j;
  }

  int* p = a;
  int* q = b;
  int* r = c;

  add(N, p, q, r);

  for(i = 0; i < 3; i++)
    sassert(c[i] >= 0);

  return 42;
}