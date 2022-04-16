/*@ requires n >= 0;
  @ decreases n + 1;
  @ ensures \result == n * (n - 1) / 2;
  @*/
int sum(int n) {
  int s = 0;
  /*@ loop invariant 0 <= i <= n;
    @ loop invariant s == i * (i - 1) / 2;
    @ loop variant n - i;
  */
  for (int i = 0; i < n; i = i + 1) s = s + i;
  return s;
}
