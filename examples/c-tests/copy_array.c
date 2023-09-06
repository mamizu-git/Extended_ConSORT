#include "seahorn/seahorn.h"
#define N 1000

int a[N];
int b[N];

extern int unknown1(void);

int my_abs(int x);

int my_abs(int x) {
  if (x >= 0) {
    return x;
  } else {
    return -x;
  }
}

void copy(int n, int* p, int* q);

void copy(int n, int* p, int* q) {
  if (n <= 0) {

  } else {
    if (n == 1) {
      *q = *p;
    } else {
      *q = *p;
      int* p1 = p + 1;
      int* q1 = q + 1;
      copy(n-1, p1, q1);
    }
  }
}

int main() {
  int i;
  int j = my_abs(unknown1 ());

  for (i = 0; i < N; i++)
    a[i] = j;

  int* p = a;
  int* q = b;

  copy(N, p, q);

  for(i = 0; i < 3; i++)
    sassert(b[i] >= 0);

  return 42;
}