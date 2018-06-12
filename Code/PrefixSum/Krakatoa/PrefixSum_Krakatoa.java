//@+ CheckArithOverflow = no


/*@ predicate is_Even{L}(integer x) =
  @ x%2 == 0;
@*/




public class PrefixSum_Krakatoa {
	int a [];

	public PrefixSum_Krakatoa(int [] array) {
	this.a = array;
    }

      /*@ 
      @   behavior success:
      @   	ensures (\forall int x y; 0<=x && x<=100 && y<=x ==> is_Even(x) ==>
			@																				(is_Even(y) ==> is_Even(x+y)) ==> \result);
      @//   ensures \result;
      @*/
    private static boolean evenSumLemma() { return true; }


	/*@
	  @ requires 0 <= a.length && a.length <= 1000
	  	&&  0 <= left && left <= a.length
	  	&&  0 <= right && right <= a.length;
	  @ ensures \result == (2*left - right+1);
	  @*/
	    private int leftMost(int left, int right) {
		return 2*left - right + 1;
	    }


	/*@   
	  @   requires x > 0 && is_Even(x); 
	  @   behavior success: 
	  @   	ensures \result == x/2 && \result*2 == x && \result < x; 
	  @*/
	  private static int div2 (int x) {
	    return x/2;
	  }


	/*@  
	  @   requires x >= 0;	  
	  @//   ensures (\product int i; 0 <= i && i < x; 2) ==> \result;
	  @   behavior success:
	  @   	ensures \result > 0;
	  @*/
	  private static int pow2(int x) {
		int count = 1;

		/*@ loop_invariant x >= 0 && count >= 1; 
		  @ loop_variant x-1;
		  @// loop_assigns count;
 		@*/
		while(x > 0){
			count += count;
			x--;
		}
		return count;		 		  
	  }


	 /*@ 
	   @   requires x > 0;
	   @   behavior success:
	   @   	ensures \result ==> (!is_Even(x) && (x != 1) ==> false);
	   @*/
	 private static boolean isPow2(int x){

		 /*@ loop_invariant x >= 1;
		   @ loop_variant x/2;
			 @*/
			while(x%2 == 0)
			{
				x = div2(x);
			}

			if(x==1){
				return true;
				}

			return false;
	 }

	/*@
      @   requires k >= 0;
			@ behavior success:
      @   ensures 0 <= \result && \result <= k && pow2(\result) <= k+1;
      @//   ensures k% pow2(\result+1) == pow2(\result)-1;
      @// 	ensures(\forall int z; k% pow2(z+1) == pow2(z)-1; z >= \result);
      @*/
    private static int min ( int k ) {
        int n = 0;
        /*@ loop_invariant (\forall int z; 0 <= z && z <= n; k% pow2(z+1) != pow2(z)-1 );
          @ loop_invariant 0 <= n && pow2(n) <= k+1;
          @ loop_variant k-n+1;
          @ loop_assigns \nothing;
          @*/
        while ( k% pow2(n+1) != pow2(n)-1 ) n++;
        return n;
    }

}
