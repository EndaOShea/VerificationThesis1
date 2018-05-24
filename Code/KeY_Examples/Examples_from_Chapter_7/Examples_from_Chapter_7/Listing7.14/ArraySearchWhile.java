public class ArraySearchWhile { // Listing 7.14

/*@ normal_behavior
  @ requires a != null;
  @ ensures \result == (\exists int i; 
  @                             0 <= i && i < a.length; a[i] == val);
  @*/
public boolean search(int[] a, int val) {
    int i = 0;
    /*@ maintaining !(\exists int j;  0 <= j && j < i; a[j] == val);
      @ maintaining 0 <= i && i <= a.length; 
      @ decreasing a.length - i;
      @*/
    while (i < a.length) {
        if (a[i] == val) 
            return true;
        i++;
    }
    return false;
}

}