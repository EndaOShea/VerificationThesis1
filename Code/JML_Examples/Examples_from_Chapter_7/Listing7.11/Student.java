public interface Student { // Listing 7.11

    /*@ public instance model int status;
      @ public instance model int credits;
      @ represents status = (credits < 180 ? bachelor : master);
      @*/

    /*@ public instance invariant status == bachelor || status == master;
      @ public instance invariant credits >= 0;
      @*/
    
    public static final int bachelor = 0;
    public static final int master = 1;

    /*@ pure @*/ public String getName(); 

    //@ ensures \result == status;
    /*@ pure @*/ public int getStatus();

    //@ ensures \result == credits;
    /*@ pure @*/ public int getCredits();

    //@ ensures getName().equals(n);
    public void setName(String n);

    /*@ requires c >= 0;
      @ ensures credits == \old(credits) + c;
      @*/
    public void addCredits(int c);

    /*@ requires credits >= 180;
      @ requires status == bachelor;
      @ ensures credits == \old(credits);
      @ ensures status == master;
      @*/
    public void changeStatus();
}
