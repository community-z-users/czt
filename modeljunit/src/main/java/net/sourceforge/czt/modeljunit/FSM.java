package net.sourceforge.czt.modeljunit;

/** Simple example of a finite state machine (FSM) for testing.
 */
public class FSM
{
  private int state = 0;  // 0..2

  public FSM()
  {
    state = 0;
  }

  public void init(boolean testing)
  {
    state = 0;
  }

  public boolean transition0Guard() { return state == 2; }
  public @transition void transition0(boolean testing)
  {
    if (testing) {
      System.out.println("transition0: " + state + " --> 0");
    }
    state = 0;
  }

  public boolean transition1Guard() { return state == 2; }
  public @transition void transition1(boolean testing)
  {
    if (testing) {
      System.out.println("transition1: " + state + " --> 1");
    }
    state = 1;
  }
  
  public boolean transition2Guard() { return state == 0; }
  public @transition void transition2(boolean testing)
  {
    if (testing) {
      System.out.println("transition2: " + state + " --> 2");
    }
    state = 2;
  }

  public boolean transitionNoneGuard() { return state != 1; }
  public @transition void transitionNone(boolean testing)
  {
    if (testing) {
      // leave state the same.
      System.out.println("transitionNone: " + state + " --> " + state);
    }
  }
}
