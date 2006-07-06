package support;

import jdsl.core.api.*;
import jdsl.graph.api.*;

/**
  * This class contains static methods for doing time arithmetic.
  *
  * @version JDSL 2
  */

public class TimeTable {
  
  // Compute the difference between times a and b, taking into account
  // the possiblity of crossing days.
  public static int diff(int a, int b) {
    int result = (a - b) % 1440;

    if (result < 0) 
      result += 1440;

    return result;
  }

}
