package q1_2012;

final class PrefixSumRec {

    /*@ spec_public @*/ private final int[] a;
       
    //@//**accessible \inv: \singleton(a);   
    //@ axiom evenSumLemma();
 
    
    /*@ requires array.length>0;
	  @ requires array!=null;
	  @// requires isPow2(a.length);
      @ ensures a.length>0 && a!= null;
    @*/
    PrefixSumRec(int [] array) {
	this.a = array;
    }

    /*@ normal_behavior
      @//   ensures \result == (\forall int x, y; even(x) == (even(y) == even(x+y))); //if x and y are even then so is x+y
      @   ensures \result;
      @   accessible \nothing;
      @   pure helper spec_public
      @*/
    private static boolean evenSumLemma() { return true; }

    /*@ normal_behavior
    @//  ensures (\exists int y;y*2 == x) == \result;
    @//  ensures (\exists int y;y*2 == x+1) != \result;
    @   accessible \nothing;
    @   pure helper spec_public
    @*/
	private static boolean even (int x) { return x%2==0;}
 	

  
	  /*@ public normal_behavior
	  @   requires x >= 0;
	  @//   ensures \result == (\product int i; 0 <= i && i < x; 2);
	  @//   ensures \result > x;
	  @   accessible \nothing;
	  @   measured_by x;
	  @   pure helper spec_public
	  @*/
	  private static int pow2(int x) {
		  //return x==0? 1: 2*pow2(x-1);
		  int result = 1;
		  
		  while(x>0)
		  {
			  result *= 2;
			  x--;
		  }
		  return result;
		  
	  }
	  	

	  
	  /*@ normal_behavior
	  @   requires x > 0;
	  @   requires even(x);
	  @//   ensures \result*2 == x;
	  @   ensures \result == x/2;
	  @   ensures \result < x;
	  @   accessible \nothing;
	  @   pure helper spec_public
	  @*/
	  private static int div2 (int x) {
	    return x/2;
	  }
	  	
	  
     /*@ normal_behavior
	    @   requires x > 0;
	    @//   ensures \result ==> ((even(x)  && isPow2(div2(x))) <=!=> x == 1); // x is a power of 2 if it:
	     																		// x == 1 or
	    																		// even and x/2 is also a power of 2 that
	    																		// will recursively go down to 1 if a power of 2
	    @//   ensures \result == (\exists int b; 0 <= b; x == (\product int i; 0 <= i && i < b; 2));
	    @   measured_by x;
	    @   accessible \nothing;
	    @   pure helper spec_public
	    @*/
	  private static boolean isPow2(int x){
	    if (x==1) 
	        return true;
	    else if (x % 2 != 0 ) 
	        return false;
	    else 
	        return isPow2(x/2);
	  }
	  
	/*@ normal_behavior
	  @ requires left >= 0 && left <= 1000000;
	  @ requires right >= 0 && right <= 1000000;
	  @ pure spec_public
	 @*/
    private /*@ helper @*/ static int leftMost(int left, int right) {
    	return 2*left - right + 1;
    }
    
    
    /*@ normal_behavior //ß\label{lst:min-begin}ß
    @   requires k >= 0 && k<=1000;
    @   ensures 0 <= \result && \result <= k;
    @   ensures pow2(\result) <= k+1;
    @   ensures k% pow2(\result+1) == pow2(\result)-1;
    @   ensures (\forall int z; k% pow2(z+1) == pow2(z)-1; z >= \result);
    @   accessible \nothing;
    @   pure helper spec_public
    @*/
	  private static int min ( int k ) {
	      int n = 0;
	      /*@ assignable \nothing;
	        @ maintaining (\forall int z; 0 <= z && z < n; k% pow2(z+1) != pow2(z)-1 );
	        @// maintaining 0 <= n && pow2(n) <= k+1;
	        @ decreasing k-n+1;         
	        @*/
	      while ( k% pow2(n+1) != pow2(n)-1 ) n++;
	      return n;
	  }//ß\label{lst:min-end}ß
  
  
}


final class Runner{
	public static void main(String[] args)
	{		
		PrefixSumRec p = new PrefixSumRec(new int [5]);
		//System.out.println(p.pow2(0));
	}
}
