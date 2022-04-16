/*@ predicate p (integer x) = x + 1 > 0; */

/*@ requires \true;
    ensures \result == a + b; */
int add(int a, int b) {
  return a + b;
}