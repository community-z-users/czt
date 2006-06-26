/**
  * A bid. 
	*
	* @author Robert Cohen (rfc)
	* @version JDSL 2
  */
public class Bid {
  private String name;
  private double amount;
  
  public Bid(String name, double amount) {
    this.name = name;
    this.amount = amount;
  }
  
  public void setAmount(double amount) {
    this.amount = amount;
  }
  
  public double amount() {
    return amount;
  }
  
  public String name() {
    return name;
  }
  
  public String toString() {
    return name + " bids " + amount;
  }
}

