final class PowerOfTwo {


    /*@ normal_behavior
      @   requires x >= 0;
      @   ensures \result == (\product int i; 0 <= i && i < x; 2);
      @   ensures \result > x;
      @   accessible \nothing;
      @   measured_by x;
      @ strictly_pure helper
      @*/
    private static int pow2( int x ) {
      return x==0? 1: 2*pow2(x-1);
    }

}
