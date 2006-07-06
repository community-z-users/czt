package support;

/**
 * Data bucket holding information about an airport.
 *
 * @version JDSL 2
 */

public class AirportSpecs {

  private String code_, name_;
  private int gmtOff_;
  private int x_, y_;
  private String label_;
  
  // accessors
  /**
   * @return the 3-letter code of the airport (PVD, etc)
   */
  public String code() { return code_; }
  
  /**
   * @return the full name of the airport (Providence T.F. Green, etc)
   */
  public String name() { return name_; }
  

  /** The GMT offset is the number of minutes to be added to transform
   *  from Greenwich Mean Time to local airport time.  In the United States,
   *  this number is negative.  To transform local airport time to GMT,
   *  you need to subtract the offset, which means subtracting a negative
   *  number.
   */
  public int GMToffset() { return gmtOff_; }
  
  /**
   * @return the x position (in pixels) of the airport on the map
   */
  public int x() { return x_; }
  
  
  /**
   * @return the y position (in pixels) of the airport on the map
   */
  public int y() { return y_; }
  
  /**
   * @return the time zone, in hhmm format (i.e. -500)
   */
  public String timeZone() {
    return Integer.toString(gmtOff_/60) +
      Integer.toString(gmtOff_%60) ;
  }
  
  /**
   * @return The String with which the vertex representing this airport was labelled
   */
  public String label() { return label_; }

  /**
   * Labels the AirportSpecs instance with the given Object.
   * This Object may be used to hold special scratch information.
   *
   * @param <i>label</i> The label with which to mark the AirportSpecs
   */
  public void setLabel(String label) { label_ = label; }
  

  /**
   * Initializes an airport specification.
   *
   * @param <i>code</i> Airport code
   * @param <i>city</i> City in which it is located
   * @param <i>gmtOffset</i> is a GMT offset of this city
   * @param <i>x</i>  x-coordinate on the map 
   * @param <i>y</i>  y-coordinate on the map
   */
  public AirportSpecs(String code, String city,
	       int gmtOffset, int x, int y) {
    code_ = code;
    name_ = city;
    
    gmtOff_ = gmtOffset;
    
    x_ = x;
    y_ = y;
    label_ = name_ + " (" + code_ + ")";
  }
  
  /** 
   * Gives a string in a format useful for debugging.  (If you have an
   * AirportSpecs a, you can just <code>System.err.println(a)</code>.)
   *
   * @return A string corresponding to the airport.
   */
  public String toString() {
    return code_ + " " + name_ + " at (" + x_ + "," + y_ 
      + ") with GMT offset " + gmtOff_;
  }
}  
// end class def



