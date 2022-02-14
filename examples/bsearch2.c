/*@ requires n >= 0 && \valid(t+(0..n-1));
  @@ assigns @ \nothing; @@
   ensures -1 <= \result <= n-1;
   behavior success:
     ensures \result >= 0 ==> t[\result] == v;
   behavior failure:
     assumes t_is_sorted : \forall integer k1, int k2;
         0 <= k1 <= k2 <= n-1
                ==> t[k1] <= t[k2];
      ensures \result == -1 ==>
       \forall integer k; 0 <= k < n ==> t[k] != v;
  */
int bsearch(double t[], int n, double v) {
  int l = 0, u = n-1;
  /*@ loop invariant 0 <= l && u <= n-1;
     for failure: loop invariant
       \forall integer k; 0 <= k < n && t[k] == v ==> l <= k <= u;
    */
  while (l <= u ) {
    int m = l + (u-l)/2; // better than (l+u)/2
    if (t[m] < v) l = m + 1;
    else if (t[m] > v) u = m - 1;
    else return m;
  }
  return -1;
}