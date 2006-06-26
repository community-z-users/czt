import java.awt.event.*;
import jdsl.core.api.*;
import jdsl.core.ref.*;

/**
	* Simulates an auction in a GUI.
	* @author Robert Cohen (rfc)
	* @version JDSL 2
	*/
public class AuctionSimulator implements CountDownTimerListener, ActionListener
{
  private AuctionFrame frame;
  private CountDownTimer clock;
  private String item[]={"Car","Watch","Elvis Painting","Computer","Chair"};
  private Position myPos;
  private Auction auction;
  private java.util.Random rnd = new java.util.Random();
  private boolean closed;
  private Sequence participants;

  // running this class just creates a visible AuctionSimulator window  
  static public void main(String args[]) {
    (new AuctionSimulator()).frame.setVisible(true);
  }

  // open a window and start things running
  AuctionSimulator(){
    frame = new AuctionFrame(this); 
    clock = frame.clock;
    reset();
  }    

  // refresh everything, but don't start the countdown
  private void reset(){
    frame.startBtn.setEnabled(true);
    frame.withdrawBtn.setEnabled(false);
    frame.setBid("");
    auction = new Auction();
    clock.reset();
    frame.clear();
    chooseItem();
    closed = false;
    myPos=null;
    participants=new ArraySequence();
  }
  
  // start the timed auction
  private void start(){
    if (closed)
      frame.setMsg("Auction closed.");
    else {
      frame.startBtn.setEnabled(false);
      myBid();
      updateFrame();
      clock.start();
    }
  }

  // action when the Withdraw button is clicked
  private void withdraw(){
    frame.withdrawBtn.setEnabled(false);
    auction.quit(myPos);
    myPos=null;
    updateFrame();
    frame.setMsg("");
  }

  // finish the auction  
  private void close() {
    closed=true;
    Position winner = auction.close();
    if  (winner == null) 
      frame.setMsg("Closed with no bidders.");
    else if (winner == myPos) 
      frame.setMsg("You win!!");
    else
      frame.setMsg("Auction closed.");
  }
  
  // receive AWT events and dispatch them to other methods
  public void actionPerformed(java.awt.event.ActionEvent event)
    {
      Object object = event.getSource();
      if (object == frame.startBtn) {
	start();
      } 
      else if (object == frame.withdrawBtn){
	withdraw();
      }
      else if (object == frame.resetBtn) {
	reset();
      }
      else if (object == frame.bidField) {
	if (closed) {
	  frame.setMsg("Bids have closed.");
	} else if (clock.isRunning()) {
	  myBid();
	} else {
	  start();
	}
      }
    }
  
  // on clock ticks, possibly end the auction or call a new bid
  public void timerTicked(CountDownTimerEvent e) {
    int timeLeft = e.timeLeft();
    if (timeLeft==0) 
      close();
    else if (timeLeft%5==0)
      newBid();
  }

  // generate a new bid from a "participant"
  private void newBid() {
    Position newPos;
    int size=participants.size();
    int choice=rnd.nextInt(size+2)-1;
    if (choice < 0) return;
    double bidAmount = auction.highBid()+rnd.nextInt(50);
    if (choice == size)
      newPos = bid(null,"",bidAmount);
    else {
      Position pos = (Position)participants.atRank(choice);
      Position bidder = (Position)pos.element();
      Position newBidder = bid(bidder,"",bidAmount);
      participants.replaceElement(pos,newBidder);
    }
  }
  
  // enter the user's bid
  private void myBid() {
    double bid = frame.getBid();
    String name = frame.getName();
    myPos=bid(myPos,name,bid);
    if (myPos != null)
      frame.withdrawBtn.setEnabled(true);
  } 

  // enter a bid
  private Position bid(Position pos, String name, double bid) {
    Position ret=pos;
    String msg = "";
    if (bid>0) {
      if (pos == null) {
	try {
	  ret=auction.initial(name,bid);
	} catch (InvalidBidException e){ 
	  msg=e.getMessage();
	}
      } else {
	try {
	  ret=auction.top(myPos,bid);
	} catch (InvalidBidException e){
	  msg=e.getMessage();
	}
      }
    }
    updateFrame();
    frame.setMsg(msg);
    return ret;
  }
  
  private void updateFrame() {
    frame.setHighBid(auction.highBid());
    frame.setNumBidders(auction.numBidders());
  }
  private void chooseItem(){
    int i = rnd.nextInt(item.length);
    frame.setItem(item[i]);
  }
}

