import jdsl.core.api.*;
import jdsl.core.ref.*;

/**
 * Simulates an auction.  New bids always must exceed the
 * current highest bid.
 *
 * @author Robert Cohen (rfc)
 * @version JDSL 2
 */
public class Auction {

    /* ************************************ */ 
    /* The members described in the lesson. */
    /* ************************************ */ 

    //b3.1
    private Sequence bids = new NodeSequence();
    private double highBid;
    //e3.1

    /**
     * Place an initial bid for a person.
     */
    //b3.2
    public Position initial(String name, double amount) throws InvalidBidException{
        checkBid(amount);
        Bid b = new Bid(name, amount);
        highBid=amount;
        return bids.insertLast(b);
    }
    //e3.2
  
    /**
     * Perform validity checks on a bid.
     */
     //b3.3
    private void checkBid(double amount) throws InvalidBidException {
        if (closed)
            throw new InvalidBidException("Bids have closed.");
        if (amount<=0) 
            throw new InvalidBidException("Bid must be positive.");
        else if (amount <= highBid)
            throw new InvalidBidException("Bid must top current high bid.");
    }
    //e3.3
  
    /**
     * Top the current high bid for someone already in the auction.
     */
    //b3.4 
    public Position top(Position p, double amount) throws InvalidBidException {
        checkBid(amount);
        Bid b = (Bid)p.element();
        b.setAmount(amount);
        try {
            bids.remove(p);
        } catch (InvalidAccessorException e) {
            throw new InvalidBidException("Bidder not in Auction.");
        }
        highBid=amount;
        return bids.insertLast(b);
    }
    //e3.4
  
    /**
     * Remove someone from the auction.
     */
    //b3.5 
    public void quit(Position p) {
        bids.remove(p);
        if (bids.size()==0)
            highBid=0;
        else
            highBid=((Bid)bids.last().element()).amount();
    }
    //e3.5
  
    /* ************************************ */ 
    /* Members not described in the lesson. */
    /* ************************************ */ 
    
    private boolean closed=false;
  
    /**
     * Place an initial bid for an amount 1 more than the
     * current highest bid.
     */
    public Position initial(String name) throws InvalidBidException{
        return initial(name, highBid+1);
    }
  
    /**
     * Top the current high bid for someone already in the auction
     * for an amount 1 more than the current highest bid.
     */
    public Position top(Position p) throws InvalidBidException {
        return top(p, highBid+1);
    }
  
    public int numBidders(){
        return bids.size();
    }    
  
    /**
     * Close the auction and print the results.
     */
    public Position close() {
        closed = true;
        if (bids.size() == 0)
            return null;
        else {
            return bids.last();
        }
    }
  
    public double highBid() {return highBid;}
  
    /**
     * Overrides the default.
     */
    public String toString() {
        String ret = "";
        if (bids.size()==0)
            return ret;
        for(int i=0; i<bids.size()-1; ++i)
            ret += ((Bid)bids.atRank(i).element()).toString() +'\n';
        ret += ((Bid)bids.atRank(bids.size()-1).element()).toString();
        return ret;
    }
 }
