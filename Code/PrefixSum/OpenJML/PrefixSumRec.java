package q1_2012;

final class PrefixSumRec {

    /*@ spec_public @*/ private final int[] a;  
    /*@ spec_public @*/ private static int count = 1;
    
    //@ invariant a.length > 0;
    //@ invariant a != null;
       
    //@ axiom evenSumLemma(); //axiom means assume named predicate is true
 
    
    /*@ requires array.length>0;
	  @ requires array!=null;
      @ ensures a.length>0 && a!= null;
    @*/
    PrefixSumRec(int [] array) {
	this.a = array;
    }
   
	    /*@ normal_behavior
	    @   ensures \result == (\forall int x, y; 0<=x && x<=100 && y<=x; even(x) == (even(y) == even(x+y))); //if x and y are even then so is x+y
	    @   ensures \result;
	    @   accessible \nothing;
	    @   pure helper spec_public
	    @*/
	  	private static boolean evenSumLemma() { 
		  return true; 
	  }
 
	  /*@ normal_behavior
	  @   ensures \result == (x%2==0);
	  @   accessible \nothing;
	  @   pure helper spec_public
	  @*/
	  	private static boolean even (int x) {
			return x%2==0;
	   }
    
    /*@ normal_behavior
	  @   requires x > 0;
	  @   requires even(x);
	  @   ensures \result*2 == x;
	  @   ensures \result == x/2;
	  @   ensures \result < x;
	  @   accessible \nothing;
	  @   pure helper spec_public
	  @*/
	  private static int div2 (int x) {
	    return x/2;
	  }
	  
	  /*@
	  @ requires 0 <= a.length && a.length <= Integer.MAX_VALUE / 2;
	  @ requires 0 <= left && left <= a.length;
	  @ requires 0 <= right && right <= a.length;
	  @ pure spec_public
	  @*/
	    private /*@ helper @*/ int leftMost(int left, int right) {
		return 2*left - right + 1;
	    }

	 
	    //@ ensures \result == (x==1||x==2||x==4||x==8||x==16||x==32);
		//@ model public pure helper static boolean _isPow2(int x);
	  
			/*@ normal_behavior
		   @   requires x > 0 && x < 33;
		   @   ensures \result ==> ( even(x) != (x == 1) );
		   @   ensures \result <==> _isPow2(x);
		   @   pure helper spec_public
		   @*/
		 private static boolean isPow2(int x){			 
			 /*@ 		   
			   @ maintaining x > 0 && x < 33;
			   @ maintaining _isPow2(\old(x)) == _isPow2(x); 
			   @ decreases x; 
				 @*/
				while(x%2 == 0)			{
					x = div2(x);
				}

				if(x==1){
					return true;
				}

				return false;
		 }

	
		/*@   requires x > 0 && x < Integer.MAX_VALUE/2;
		  @   ensures \result/2 == x;
		  @   ensures \result == x*2;
		  @   ensures \result > x;
		  @   accessible \nothing;
		  @   pure helper spec_public
		  @*/
		  private static int mult2 (int x) {
		    return x*2;
		  }
		 		    
		/*@ public normal_behavior
		  @   requires x >= 0;
		  @   ensures \result > 0 && \result < 33;
		  @   assignable count;
		  @   spec_public
		  @*/
		  private static long pow2(int x) {
			count = 1;

		   /*@ 
			 @ maintaining x >= 0;
			 @ maintaining _isPow2(count);
			 @ decreases x;
			@*/
			while(x>0)
			{
			 //@ assume x!=0;
			if(count < 33)
			 count = mult2(count);
			 x--;
			}
			
			//@ assume x==0;
			return count;	  		 		  
		  }	  
	 
}


final class Runner{
	public static void main(String[] args)
	{		
		PrefixSumRec p = new PrefixSumRec(new int [4]);
		//System.out.println(p.pow2(0));4
	}
}
