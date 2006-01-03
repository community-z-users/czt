package support;
import jdsl.core.api.Dictionary;

/**
 * Data bucket that holds information about a flight.
 * @version JDSL 2
 */

public class FlightSpecs
{
  private String airline_;
  private int number_;
  private String srcCode_, destCode_;
  private int deptime_;
  private int arrtime_;
  private int localdeptime_;
  private int localarrtime_;
  private String plane_;
  private String fares_;
  private int cargoCapacity_;
  private String label_;
  
  /** 
   * Parses a line from a file into a data object representing the
   * flight info.
   *
   * @param line String from a flight database file
   * @param airports Dictionary of (String airportcode, AirportSpecs element)
   */
  public FlightSpecs (String airline, int flightnum, 
		      String origin, String destination,
		      int localDepTime, int localArrivalTime,
		      int gmtDepTime, int gmtArrivalTime,
		      String plane, String fares, int cargo)
    {
      airline_ = airline;
      number_ = flightnum;
      srcCode_ = origin;
      destCode_ = destination;
      localdeptime_ = localDepTime;
      localarrtime_ = localArrivalTime;
      deptime_ = gmtDepTime;
      arrtime_ = gmtArrivalTime;
      plane_ = plane;
      fares_ = fares;
      cargoCapacity_ = cargo;
      label_ = ticketString();
    }
  
  // accessors
  /**
   * @return the airline (PA, UA, AC, etc)
   */
  public String airline() { return airline_ ; }
  
  /**
   * @return the flight number (TW 800 yields 800, AC8813 yields 8813, etc)
   */
  public int flightNumber() { return number_ ; }
  
  /**
   * @return the 3-letter code of the airport the flight left (PVD, LAX, etc)
   * @see support.flight.AirportSpecs#code
   */
  public String originCode() { return srcCode_ ; }
  
  /**
   * @return the 3-letter code of the airport the flight goes to (PVD, etc)
   * @see support.flight.AirportSpecs#code
   */  
  public String destinationCode() { return destCode_ ; }
  
  /**
   * @return the departure time of the flight, in GMT minutes since midnight
   */
  public int departureTime() { return deptime_ ; }
  
  /**
   * @return the arrival time of the flight, in GMT minutes since midnight
   */
  public int arrivalTime() { return arrtime_ ; }
  
  /**
   * @return the airliner type (737, DC8, Wright Brothers, etc)
   */
  public String planeType() { return plane_; }
  
  /**
   * @return the fares available (Y, Q, H, F, P, etc; dunno what they mean)
   */
  public String fareCodes() { return fares_; }
  
  /**
   * @return The available cargo capacity of the aircraft.
   */
  public int cargoCapacity() { return cargoCapacity_; }
  
  /**
   * @return The Object with which the edge representing this flight was labelled.
   */
  public String label() { return label_; }
  
  /**
   * Labels or marks the FlightSpecs instance with the given Object.
   * This Object may be used to hold special scratch information.
   *
   * @param Object The label with which to mark the FlightSpec
   */
  public void setLabel(String label) { label_ = label; }

  /**
   * Computes the duration of the flight. 
   *
   * @return int minutes
   */
  public int flightDuration() {
    return TimeTable.diff(arrivalTime(),departureTime());
  }
  
  /** 
   * Gives a string in a form useful for debugging.  (If you have 
   * a FlightSpecs f, you can just <code>System.err.println(f)</code>.)
   *
   * @return String representing the flight
   */
  public String toString() {
    return airline_ + number_ + " from " + srcCode_ + " at " + deptime_ +
      " to " + destCode_ + " at " + arrtime_;
  }
  
  /** 
   * Gives a string in a form useful for printing out itineraries.
   * Note the times are given in local time of the airport, so
   * a flight 
   * <pre>  AC8813 YHZ 1200N BOS 1235P DH8 Y Q H P F</pre>
   * Leaves YHZ at noon Atlantic time and arrives in Boston at 12:35 Eastern
   * time.  So it takes 1:35, not 35 minutes.
   *
   * @return String that should be printed on console to show itinerary
   */
  public String ticketString() {
    String toReturn = airline() + " ";
    String flightNum = "" + flightNumber();
    flightNum = frontPad(flightNum, 4);
    toReturn += flightNum;
    toReturn += " " + originCode() + " " +  
      StandardOps.printTime(localdeptime_) + " " +
      destinationCode() + " " +
      StandardOps.printTime(localarrtime_) + " " +
      frontPad(planeType()+"", 3) + " " + fareCodes();

    return toReturn;
  }
  
  private String frontPad(String toPad, int space) {
    space = space - toPad.length();
    if (space <= 0) return toPad;
    while (space != 0) {
      toPad = " " + toPad;
      space--;
    }
    return toPad;
  }

}
