/*@ requires n <= 12;
    decreases n;
  */
int fact(int n) {
  if (n <= 1) return 1;
  return n * fact(n-1);
}

//@ decreases n;
int fib(int n) {
  if (n <= 1) return 1;
  return fib(n-1) + fib(n-2);
}