package net.sourceforge.czt.modeljunit;

/** Simple example of a finite state machine (FSM) for testing.
 */
public class FSM
{
  private int state = 0;  // 0..2
  private boolean testing = false;

  public FSM()
  {
    state = 0;
  }

  public void init(boolean startTesting)
  {
    state = 0;
    testing = startTesting;
  }

  public boolean transition0Guard() { return state == 2; }
  public @Action void transition0()
  {
    if (testing) {
      System.out.println("transition0: " + state + " --> 0");
    }
    state = 0;
  }

  public boolean transition1Guard() { return state == 2; }
  public @Action void transition1()
  {
    if (testing) {
      System.out.println("transition1: " + state + " --> 1");
    }
    state = 1;
  }
  
  public boolean transition2Guard() { return state == 0; }
  public @Action void transition2()
  {
    if (testing) {
      System.out.println("transition2: " + state + " --> 2");
    }
    state = 2;
  }

  public boolean transitionNoneGuard() { return state != 1; }
  public @Action void transitionNone()
  {
    if (testing) {
      // leave state the same.
      System.out.println("transitionNone: " + state + " --> " + state);
    }
  }
}
