class Average2 { // Listing 7.9

    /*@ spec_public @*/ private Student[] sl;

    /*@ normal_behavior
      @ requires sl.length > 0;
      @ ensures \result == 
      @         (\sum int i; 0 <= i && i < sl.length; 
      @                      sl[i].getCredits())/sl.length;
      @ also
      @ exceptional_behavior
      @ requires sl.length == 0;
      @ signals_only ArithmeticException;
      @ signals (ArithmeticException e) true;
      @*/
    public int averageCredits() {
	int sum = 0;
	for (int i = 0; i < sl.length; i++) {
	    sum = sum + sl[i].getCredits();
	};
	return sum/sl.length;
    }
}
