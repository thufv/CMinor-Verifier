/*@ predicate p (int x) = x + 1 > 0; */

/*@ requires \true;
    ensures \result == \old(a) + b; */
int add(int a, int b) {
  int c = a + b;
  a = 2;
  return c;
}