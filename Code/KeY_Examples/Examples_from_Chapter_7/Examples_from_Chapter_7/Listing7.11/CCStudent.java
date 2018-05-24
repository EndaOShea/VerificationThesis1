public class CCStudent implements Student { // Listing 7.11

    private int[] creditList;

    /*@ private represents credits =
      @     (\sum int i; 0 <= i && i < creditList.length; creditList[i]);
      @*/

    // rest of class continued...
}
