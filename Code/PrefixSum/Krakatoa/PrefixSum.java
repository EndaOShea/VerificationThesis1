//@+ CheckArithOverflow = no


/*@ predicate is_Even{L}(integer x) =
  @ x%2 == 0;
@*/

/*@ predicate is_Pow2{L}(integer x) =
  @ (x==1||x==2||x==4||x==8||x==16||x==32);
@*/


public class PrefixSum {
	int a [];

	public PrefixSum(int [] array) {
	this.a = array;
    }

      /*@ 
			@		assigns \nothing;
      @   behavior success:
      @   	ensures (\forall int x y; 0<=x && x<=100 && y<=x ==> is_Even(x)
			@												 															 ==>(is_Even(y)
			@ 																										 ==> is_Even(x+y))
			@ 																										 ==> \result);
      @*/
    private static boolean evenSumLemma() { return true; }


	/*@
	  @ requires 0 <= a.length && a.length <= 1000
	  	&&  0 <= left && left <= a.length
	  	&&  0 <= right && right <= a.length;
		@	assigns \nothing;
	  @ ensures \result == (2*left - right+1);
	  @*/
	    private int leftMost(int left, int right) {
		return 2*left - right + 1;
	    }


	/*@  		 
	  @   requires x > 0 && is_Even(x);
		@		assigns \nothing; 
	  @   behavior success: 
	  @   	ensures \result == x/2 && \result*2 == x && \result < x; 
	  @*/
	  private static int div2 (int x) {
	    return x/2;
	  }


	/*@  
	  @   requires x >= 0;
		@		assigns \nothing;	  
	  @   behavior success:
	  @   	ensures (\result > 0  <==> is_Pow2(\result));	
	  @*/
	  private static int pow2(int x) {
		int count = 1;

		/*@
		  @ loop_invariant x >= 0 && count >= 1 && is_Pow2(\old(count) <==> is_Pow2(count));
		  @ loop_variant x-1;
 		@*/
		while(x > 0){
			count += count;
			x--;
		}
		return count;		 		  
	  }


		

	 /*@ 
	   @   requires x > 0 && x < 33;
		 @	 assigns \nothing;		 
	   @   behavior success:
	   @   	ensures \result <==> is_Pow2(x);
	   @*/
	 private static boolean isPow2(int x){

		 /*@ loop_invariant x >= 1 && x < 33;
		   //&& is_Pow2(\old(x)) <==> is_Pow2(x);
		   @ loop_variant x;
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


}
