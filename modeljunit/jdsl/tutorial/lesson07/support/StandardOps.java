package support;

/**
 * Some utility operations the support code uses. 
 *
 * @version JDSL 2
 */
public class StandardOps {
  public static final int NOON = 12*60 ;

  /** 
    * Creates a string corresponding to the integer with the specified
    * width and left-fill.  The width is a minimum; if the integer does
    * not fit, it will be wider.<p>
    *
    * Example:
    * <pre>  StandardOps.printInt(1, 5, '0'); </pre>
    * will print
    * <pre>  00001</pre>
    *
    * @param toprint The integer to print
    * @param width   The minimum width of the integer
    * @param fill    The character with which to left-fill the string
    * @return        The String corresponding to the integer.
    */

  static public String printInt(int toprint, int width, char fill) {
    String intStr = String.valueOf(toprint);
    int i = width - intStr.length();
    if(i>0) {
      char retval[] = new char[i];
      for(int j=0; j<i; j++) {
	retval[j] = fill;
      }
      return new String(retval) + intStr;
    }
    else {
      return intStr;
    }
  }
  /**
    * Similar to above, but fills with a String.  Not too useful.
    * <p>
    *
    * Example:
    * <pre>  StandardOps.printInt(1, 5, "abcde"); </pre>
    * will print
    * <pre>  abcd1</pre>
    *
    * @param toprint The integer to print
    * @param width   The minimum width of the integer
    * @param fill    The filler string; uses the substring corresponding to
    *                the first <i>i</i> characters of the filler, where
    *                <i>i</i> is the amount of room free.  
    * @return        The String corresponding to the integer.
    */

  static public String printInt(int toprint, int width, String fill) {   
    String intStr = String.valueOf(toprint);
    int i = width - intStr.length();
    if (i>=0) {
      String filler = fill.substring(0,i+1);
      return new String(filler + intStr);
    }
    else 
      return intStr;
  }


  /**
    * Creates a string corresponding to the time.
    * The time is assumed to be in minutes since midnight.
    * The output format is hhmmM -- that is, 2-digit hours, 2-digit minutes,
    * 1-character meridian.  Hours and minutes are left-filled with zeros.
    * Note 1259P is one minute before 0100P.<p>
    *
    * Example:
    * <pre>  StandardOps.printTime(60); </pre>
    * will print
    * <pre>  0100A</pre>
    *
    * @param time The time to print, in minutes since midnight.
    * @return     The String corresponding to the time, formatted as on
    *             airplane tickets.
    */
  static public String printTime(int time) {
    int hours = (int)time/60;
    int minutes = (int)time%60;
    char meridian = 'A';
    if(hours >= 12) {
      if((hours>12)) { hours -= 12; }
      meridian = 'P';
    }
    else if(hours==0) {
      hours=12;
    }
    return printInt(hours,2,' ') + ":" + printInt(minutes,2,'0') + 
      " " + meridian + "M";
  }

  /**
    * Parses a String in the format of printTime(.) as a time.
    * Takes a string in the format hhmmM and returns the number
    * of minutes since midnight to which the string corresponds.
    * Throws an IllegalArgumentException if the conversion fails.<p>
    *
    * Example:
    * <pre>  StandardOps.parseTime("0100A"); </pre>
    * will return 60.
    *
    * @param str The string to parse.
    * @return    The corresponding number of minutes since midnight.
    * @exception IllegalArgumentException if the string cannot
    *            be converted (it is too short, or the meridian
    *            field is not A, P, or is not a valid time).
    */
  static public int parseTime(String str) throws IllegalArgumentException {

    int meridianOffset = 0;
    boolean useHoursFromMidnight = false;
    switch(str.charAt(str.length() - 1)) {
    case 'P':
    case 'p':
      meridianOffset = NOON;
      str = str.substring(0, str.length() - 1);
      break;
    case 'a':
    case 'A':
      str = str.substring(0, str.length() - 1);
      break;
    case '0':
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7':
    case '8':
    case '9':
      useHoursFromMidnight = true;
      break;
    default:
      throw new IllegalArgumentException("Unparsable time");
    }
    if(str.length() < 3)
      throw new IllegalArgumentException("Unparsable time");
    int strint;
    try {
      strint = Integer.parseInt(str);
    }
    catch (NumberFormatException e) {
      throw new IllegalArgumentException(e.getMessage());
    }
    if(strint < 0) throw new IllegalArgumentException("Negative time");
    int minutes = strint % 100;
    if((minutes > 59) || (minutes < 0)) {
      throw new IllegalArgumentException("Invalid minute: " + minutes);
    }

    int hours = strint / 100;

    if(useHoursFromMidnight) {
      if(hours > 23) {
	throw new IllegalArgumentException("Invalid hour: " + hours);
      }
      return 60 * hours + minutes;
    }
    else {
      if(hours > 12) {
	throw new IllegalArgumentException("Invalid hour: " + hours);
      }
      return meridianOffset + (hours % 12) * 60 + minutes;
    }
  }  

  static public int toGMT(int local_time, int gmt_offset) {
    return ( ( local_time - gmt_offset ) + 1440 ) % 1440;
  }

}
