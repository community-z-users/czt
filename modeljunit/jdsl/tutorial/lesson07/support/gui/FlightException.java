package support.gui;

/**
 * Thrown by support code to indicate a fatal error, for example,
 * can't open the airport database file.
 *
 * @version JDSL 2
 */
public class FlightException extends RuntimeException {
  public FlightException(String str) {
    super(str);
  }
}
