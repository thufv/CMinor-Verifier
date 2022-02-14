//@ predicate p = \true;

/*@ requires \true;
    ensures \result == a + b; */
int add(int a, int b) {
  return a + b;
}