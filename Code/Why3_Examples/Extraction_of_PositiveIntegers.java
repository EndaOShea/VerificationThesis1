//@+ SeparationPolicy = Regions

/*@ axiomatic NumOfPos {
  @  logic integer num_of_pos{L}(integer i,integer j,int t[]);
  @  axiom num_of_pos_empty{L} :
  @   \forall integer i j, int t[];
  @    i >= j ==> num_of_pos(i,j,t) == 0;
  @  axiom num_of_pos_true_case{L} :
  @   \forall integer i j k, int t[];
  @       i < j && t[j-1] > 0 ==> 
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t) + 1;
  @  axiom num_of_pos_false_case{L} :
  @   \forall integer i j k, int t[];
  @       i < j && ! (t[j-1] > 0) ==> 
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t);
  @ }
  @*/


/*@ lemma num_of_pos_non_negative{L} :
  @   \forall integer i j, int t[]; 0 <= num_of_pos(i,j,t);
  @*/

/*@ lemma num_of_pos_additive{L} :
  @   \forall integer i j k, int t[]; i <= j <= k ==>
  @       num_of_pos(i,k,t) == num_of_pos(i,j,t) + num_of_pos(j,k,t);
  @*/

/*@ lemma num_of_pos_increasing{L} :
  @   \forall integer i j k, int t[];
  @       j <= k ==> num_of_pos(i,j,t) <= num_of_pos(i,k,t);
  @*/

/*@ lemma num_of_pos_strictly_increasing{L} :
  @   \forall integer i n, int t[];
  @       0 <= i < n && t[i] > 0 ==> 
  @       num_of_pos(0,i,t) < num_of_pos(0,n,t);
  @*/

public class Muller {

    /*@ requires t != null;
      @*/
    public static int[] m(int t[]) {
	int count = 0;
	
	/*@ loop_invariant
	  @    0 <= i <= t.length && 
	  @    0 <= count <= i && 
	  @    count == num_of_pos(0,i,t) ; 
	  @ loop_variant t.length - i;
	  @*/
	for (int i=0 ; i < t.length; i++) if (t[i] > 0) count++;
	
	int u[] = new int[count];
	count = 0;
	
	/*@ loop_invariant
	  @    0 <= i <= t.length && 
	  @    0 <= count <= i && 
	  @    count == num_of_pos(0,i,t);
	  @ loop_variant t.length - i;
	  @*/
	for (int i=0 ; i < t.length; i++) {
	    if (t[i] > 0) u[count++] = t[i];
	}
	return u;
    }
    
}