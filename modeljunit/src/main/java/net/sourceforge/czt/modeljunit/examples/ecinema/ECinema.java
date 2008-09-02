package net.sourceforge.czt.modeljunit.examples.ecinema;

import java.io.FileNotFoundException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.modeljunit.Action;
import net.sourceforge.czt.modeljunit.FsmModel;
import net.sourceforge.czt.modeljunit.GraphListener;
import net.sourceforge.czt.modeljunit.GreedyTester;
import net.sourceforge.czt.modeljunit.LookaheadTester;
import net.sourceforge.czt.modeljunit.RandomTester;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.VerboseListener;
import net.sourceforge.czt.modeljunit.coverage.ActionCoverage;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;

/**
 *  A model of a simple eCinema.
 *  That is, a web-based system for selecting and buying movie tickets.
 *
 *  For simplicity, Movie objects and Ticket objects are just
 *  modelled as strings.  Note that missing usernames and passwords
 *  are modelled as empty strings ("").
 *
 * @author marku
 *
 * LOG:
 * 3 Sep 2007: 3 hours writing model
 *      Found several guard errors due to ModelJUnit warnings
 *      NullPtr exception -> 2-3 mistakes in changing states
 *      Infinite resets -> found that showtimes[1] was not init properly
 *
 *      State Graph showed it was not reaching displayTickets state.
 *         (took a couple of hours to realise that registration was not
 *          resetting the state to "welcome"!)
 */
public class ECinema implements FsmModel
{
  /** Each of these states models a separate web page.
   *  (Except for terminal, which means that the session is finished.)
   */
  public enum State {welcome, register, displayTickets, terminal};

  public State state = State.welcome;

  /** This is the most recent message that has been output. */
  public String message = null;

  public User currentUser = null;

  /** This maps each username to the User object. */
  public Map<String,User> allUsers = new HashMap<String,User>();

  public Showtime[] showtimes = new Showtime[2];

  public Object getState()
  {
    return state.toString()
       //+ "[" + message + "]"
       + ((currentUser==null) ? "" : "_"+currentUser.name);
  }

  public void reset(boolean testing)
  {
    state = State.welcome;
    message = null;
    currentUser = null;

    // one registered user
    allUsers = new HashMap<String,User>();
    allUsers.put("ERIC", new User("ERIC", "ETO"));

    // two showtimes
    showtimes[0] = new Showtime();
    showtimes[0].dateTime = Showtime.DATE_CORRECT;
    showtimes[0].movie = "Star Wars I";
    showtimes[0].tickets = new HashSet<String>();
    for (int i=1; i<= 3; i++)
      showtimes[0].tickets.add("ticket"+i);
    showtimes[0].ticketsLeft = showtimes[0].tickets.size();

    showtimes[1] = new Showtime();
    showtimes[1].dateTime = Showtime.DATE_CORRECT;
    showtimes[1].movie = "Star Wars II";
    showtimes[1].tickets = new HashSet<String>();
    for (int i=4; i<= 10; i++)
      showtimes[1].tickets.add("ticket"+i);
    showtimes[1].ticketsLeft = showtimes[1].tickets.size();
  }

  public boolean loginEmptyGuard() {return loginGrd(); }
  public boolean loginEricOkGuard() {return loginGrd(); }
  public boolean loginEricBadGuard() {return loginGrd(); }
  public boolean loginAmandineOkGuard() {return loginGrd(); }
  public boolean loginAmandineEmptyGuard() {return loginGrd(); }

  @Action public void loginEmpty() { login("", "ETO"); }
  @Action public void loginEricOk() { login("ERIC", "ETO"); }
  @Action public void loginEricBad() { login("ERIC", "ACH"); }
  @Action public void loginAmandineOk() { login("AMANDINE", "ACH"); }
  @Action public void loginAmandineEmpty() { login("AMANDINE", ""); }

  public boolean loginGrd() {return state == State.welcome;}
  public void login(String userName, String userPassword)
  {
    if (userName.equals("")) {
      message = "EMPTY_USERNAME"; /*@REQ: CIN_031 @*/
    }
    else if (userPassword.equals("")) {
      message = "EMPTY_PASSWORD"; /*@REQ: CIN_032 @*/
    }
    else if ( ! allUsers.containsKey(userName)) {
      message = "UNKNOWN_USER_NAME_PASSWORD"; /*@REQ: CIN_033 @*/
    }
    else {
      User user_found = allUsers.get(userName);
      if (user_found.password.equals(userPassword)) {
        currentUser = user_found;
        message = "WELCOME";  /*@REQ: CIN_030 @*/
      }
      else {
        message = "WRONG_PASSWORD"; /*@REQ: CIN_034 @*/
      }
    }
  }

  public boolean logoutGuard()
  {
    return currentUser != null
      && (state == State.welcome || state == State.displayTickets);
  }
  @Action public void logout()
  {
    message = "BYE";
    currentUser = null; /*@REQ: CIN_100@*/
    state = State.welcome;
  }

  public boolean buyTicketShow1Guard() {return buyTicketGrd(showtimes[0]);}
  public boolean buyTicketShow2Guard() {return buyTicketGrd(showtimes[1]);}
  @Action public void buyTicketShow1() {buyTicket(showtimes[0]);}
  @Action public void buyTicketShow2() {buyTicket(showtimes[1]);}

  public boolean buyTicketGrd(Showtime shtime)
  {
    return state == State.welcome
    && shtime.ticketsLeft >= 1
    && shtime.dateTime == Showtime.DATE_CORRECT;
  }
  /** Buy one ticket for current user, from the given shtime. */
  public void buyTicket(Showtime shtime)
  {
    if (currentUser == null) {
      message = "LOGIN_FIRST"; /*@REQ: CIN_061@*/
    }
    else {
      if (shtime.ticketsLeft == 1) {
        message = "NO_MORE_TICKET";
        shtime.buyButtonActive = false; /*@REQ: CIN_062@*/
      }
      else {
        message=null;
        shtime.buyButtonActive = true; /*@REQ: CIN_060@*/
      }
      shtime.clearAllButtonActive = currUsersTickets(shtime).size() >= 1;
      // search for an unallocated ticket [Nasty!]
      // Note: could simplify this by keeping an allocated flag in each ticket
      String free_ticket_found = null;
      for (String ticket : shtime.tickets) {
        free_ticket_found = ticket;
        for (User user : allUsers.values()) {
          if (user.tickets.contains(ticket)) {
            free_ticket_found = null;
            break;
          }
        }
        if (free_ticket_found != null)
          break;
      }
      assert free_ticket_found != null;
      currentUser.tickets.add(free_ticket_found);
      shtime.ticketsLeft--;
    }
  }


  public boolean deleteTicketShow1Guard() {return deleteTicketGrd(showtimes[0]);}
  public boolean deleteTicketShow2Guard() {return deleteTicketGrd(showtimes[1]);}
  @Action public void deleteTicketShow1() {deleteTicket(showtimes[0]);}
  @Action public void deleteTicketShow2() {deleteTicket(showtimes[1]);}

  public boolean deleteTicketGrd(Showtime shtime)
  {
    return state == State.displayTickets
      && currentUser != null
      && ! currUsersTickets(shtime).isEmpty();
  }
  public void deleteTicket(Showtime shtime)
  {
    Set<String> shtickets = currUsersTickets(shtime);
    String ticket = shtickets.iterator().next();  // choose one to delete
    shtime.clearAllButtonActive = shtickets.size() > 1;
    shtime.buyButtonActive = true;
    currentUser.tickets.remove(ticket);  /*@REQ: CIN_090@*/
  }


  public boolean deleteAllTicketsShow1Guard() {return deleteAllTicketsGrd(showtimes[0]);}
  public boolean deleteAllTicketsShow2Guard() {return deleteAllTicketsGrd(showtimes[1]);}
  @Action public void deleteAllTicketsShow1() {deleteAllTickets(showtimes[0]);}
  @Action public void deleteAllTicketsShow2() {deleteAllTickets(showtimes[1]);}

  public boolean deleteAllTicketsGrd(Showtime shtime)
  {
    return state == State.displayTickets
      && shtime.clearAllButtonActive;
  }
  public void deleteAllTickets(Showtime shtime)
  {
    shtime.ticketsLeft += currUsersTickets(shtime).size();
    currentUser.tickets.removeAll(currUsersTickets(shtime));
    shtime.clearAllButtonActive = false;  /*@REQ: CIN_080@*/
  }

  public boolean gotoRegisterGuard() { return state == State.welcome; }
  @Action public void gotoRegister()
  {
    state = State.register; /*@REQ: CIN_010 @*/
  }

  public boolean registerAmandineGuard() {return regGuard("AMANDINE");}
  public boolean registerEricGuard() {return regGuard("ERIC");}
  public boolean registerEmptyGuard() {return regGuard("");}
  @Action public void registerAmandine() {reg("AMANDINE", "ACH");}
  @Action public void registerEric() {reg("ERIC", "ACH");}
  @Action public void registerEmpty() {reg("", "ACH");}

  public boolean regGuard(String userName)
  {
    return state == State.register;
  }
  public void reg(String userName, String userPassword)
  {
    if (userName.equals("")) {
      message = "EMPTY_USERNAME"; /*@REQ: CIN_020@*/
    }
    if (allUsers.containsKey(userName)) {
      message = "EXISTING_USER_NAME"; /*@REQ: CIN_040@*/
    }
    else {
      User newUser = new User(userName, userPassword);
      allUsers.put(userName, newUser);
      currentUser = newUser;
      message="WELCOME"; /*@REQ: CIN_050@*/
      state = State.welcome;
    }
  }

  public boolean displayTicketsGuard()
  {
    return state == State.welcome;
  }
  @Action public void displayTickets()
  {
    if (currentUser == null) {
      message = "LOGIN_FIRST"; /*@REQ: CIN_063@*/
      // and stay in the welcome state
    }
    else {
      message = null; /*@REQ: CIN_070@*/
      state = State.displayTickets;
    }
  }

  public boolean backGuard() { return state == State.displayTickets; }
  @Action public void back()
  {
    state = State.welcome;
  }

  public boolean closeGuard()
  {
    // all tickets have been returned!
    return state != State.terminal
      && showtimes[0].ticketsLeft == 3
      && showtimes[1].ticketsLeft == 7;
  }
  @Action public void close()
  {
    message = null;
    currentUser = null; /*@REQ: CIN_110@*/
    state = State.terminal;
  }

  /** the current user's tickets for the given show time. */
  protected Set<String> currUsersTickets(Showtime shtime)
  {
    Set<String> result = new HashSet<String>(currentUser.tickets);
    result.retainAll(shtime.tickets);
    return result;
  }

  public static void main(String[] args) throws FileNotFoundException
  {
    Tester tester = new RandomTester(new ECinema());
    // The guards make this a more difficult graph to explore, but we can
    // increase the default maximum search to complete the exploration.
    GraphListener graph = tester.buildGraph(100000);
    graph.printGraphDot("ecinema.dot");
    CoverageMetric trans = tester.addCoverageMetric(new TransitionCoverage());
    CoverageMetric trpairs = tester.addCoverageMetric(new TransitionPairCoverage());
    CoverageMetric states = tester.addCoverageMetric(new StateCoverage());
    CoverageMetric actions = tester.addCoverageMetric(new ActionCoverage());
    tester.addListener("verbose");
    // this illustrates how to generate tests upto a given level of coverage.
    int steps = 0;
    while (actions.getPercentage() < 100 /* || steps < 1000*/) {
      tester.generate();
      steps++;
    }
    System.out.println("Generated "+steps+" steps.");
    tester.printCoverage();
  }
}
