class isPow2{

//@  ensures \result == (x == 1 || x==2 || x==4 || x==8 || x==16);
//@ model public pure helper static boolean _isPow2(int x);

//@ model public static final int MOST = 31;

/*@ normal_behavior
        @   requires x > 0 && x < Integer.MAX_VALUE;
        @   requires x <= MOST;
        @   ensures  \result <==> _isPow2(x);
        @   pure helper spec_public
        @*/
      private static boolean isPow2(int x){
          /*@
            @ maintaining x >= 1 && x <= MOST;
            @ maintaining _isPow2(\old(x)) == _isPow2(x);
            @ decreases x;
              @*/
             while(x%2 == 0){
                 x = div2(x);
             }

             if(x==1){
                 return true;
             }

             return false;
      }


     //@ ensures \result == x/2;
     //@ pure
     public static int div2(int x) {
        return x/2;
     }

     //@ ensures \result == (x%2 == 0);
     //@ pure
     public static boolean even(int x) { return x%2 == 0; }
}

}