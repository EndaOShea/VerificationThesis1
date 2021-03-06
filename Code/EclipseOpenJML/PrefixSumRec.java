package q1_2012;

final class PrefixSumRec {

    /*@ spec_public @*/ private final int[] a;  
    /*@ spec_public @*/ private static int count = 1;
       
    //@//**accessible \inv: \singleton(a);   
    //@ axiom evenSumLemma(); //axiom means assume named predicate is true
 
    
    /*@ requires array.length>0;
	  @ requires array!=null;
	  @// requires isPow2(a.length);
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
    private static boolean evenSumLemma() { return true; }

    
    
    /*@ normal_behavior
    @   ensures \result == (x%2==0);
    @   accessible \nothing;
    @   pure helper spec_public
    @*/
	private static boolean even (int x) 
	{ return x%2==0;}
	
	
    
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
	 
	    
	/*@ public normal_behavior
	  @   requires x == 3;
	  @// ensures \result == (\product int i; 0 <= i && i < x; 2);
	  @   ensures \result > 0 && \result < Integer.MAX_VALUE;
	  @// measured_by x;
	  @   assignable count;
	  @   spec_public
	  @*/
	  private static long pow2(int x) {
		 // return x==0? 1: 2*pow2(x-1);
		count = 1;

		//@ maintaining count >= 1 && x >= 0; 
		while(x>0)
		{
		 count += count;
		 x--;
		}
		return count;	  		 		  
	  }
	      
	  
		/*@ normal_behavior
	   @   requires x > 0 && x < Integer.MAX_VALUE;
	   @   ensures \result ==> ( even(x) != (x == 1) );
	   @   accessible \nothing;
	   @   pure helper spec_public
	   @*/
	 private static boolean isPow2(int x){
		 /*@ 		   
		   @ maintaining x >= 1;
		   @ decreases x/2; 
			 @*/
			while(x%2 == 0){
				x = div2(x);
			}

			if(x==1){
				return true;
			}

			return false;
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

	    	  
	 
}


final class Runner{
	public static void main(String[] args)
	{		
		PrefixSumRec p = new PrefixSumRec(new int [5]);
		//System.out.println(p.pow2(0));
	}
}
