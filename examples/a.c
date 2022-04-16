//@ predicate sorted(integer a[]) = \forall integer i; 0 <= i < \length(a) - 1 ==> a[i] <= a[i + 1];

/*@
   requires sorted(a);
 */
int search(int a[], int x) {
    return 0;
}