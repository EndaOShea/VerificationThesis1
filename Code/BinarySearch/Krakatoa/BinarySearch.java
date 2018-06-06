
//@+ CheckArithOverflow = no

/* lemma mean_property1 :
  @   \forall integer x y; x <= y ==> x <= (x+y)/2 <= y;
  @*/

/* lemma mean_property2 :
  @   \forall integer x y; x <= y ==> x <= x+(y-x)/2 <= y;
  @*/

/* lemma div2_property :
  @   \forall integer x; 0 <= x ==> 0 <= x/2 <= x;
  @*/

/*@ predicate is_sorted{L}(int[] t) =
  @   t != null &&
  @   \forall integer i j;
  @     0 <= i && i <= j && j < t.length ==> t[i] <= t[j] ;
  @*/


class BinarySearch {

    /*@ requires t != null;
      @ ensures -1 <= \result < t.length;
      @ behavior success:
      @   ensures \result >= 0 ==> t[\result] == v;
      @ behavior failure:
      @  assumes is_sorted(t);
      @  ensures \result == -1 ==>
      @    \forall integer k; 0 <= k < t.length ==> t[k] != v;
      @*/
    static int binary_search(int t[], int v) {
	int l = 0, u = t.length - 1;
	/*@ loop_invariant
	  @   0 <= l && u <= t.length - 1;
	  @ for failure:
	  @  loop_invariant
	  @    \forall integer k; 0 <= k < t.length ==> t[k] == v ==> l <= k <= u;
	  @ loop_variant
	  @   u-l ;
	  @*/
	while (l <= u ) {
	    int m;
            m = (u + l) / 2;
		//@assert l <= m <= u;
	    if (t[m] < v) l = m + 1;
	    else if (t[m] > v) u = m - 1;
	    else return m;
	}
	return -1;
    }

}
