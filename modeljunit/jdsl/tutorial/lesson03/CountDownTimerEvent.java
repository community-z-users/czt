/**
	* @author Robert Cohen (rfc)
	* @version JDSL 2
	*/
public class CountDownTimerEvent extends java.util.EventObject {
  private int timeLeft;
  
  public CountDownTimerEvent(Object source, int left) {
    super(source);
    timeLeft = left;
  }
  
  public int timeLeft() {return timeLeft;}
}
