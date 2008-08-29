
package net.sourceforge.czt.modeljunit;

import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import java.util.Random;

public class AllRoundTester extends Tester
{
  CoverageMetric state;

  int loopTolerance;

  Tester test;

  /**
   *  Creates a GreedyTester that will terminate each test
   *  sequence after {@code getLoopTolerance()} visits to a state.
   *
   * @param model  Must be non-null;
   */
  public AllRoundTester(Model model)
  {
    this(new GreedyTester(model));
  }

  /**
   * A convenience constructor that puts a Model wrapper around an FsmModel.
   * @param fsm  Must be non-null.
   */
  public AllRoundTester(FsmModel fsm)
  {
    this(new Model(fsm));
  }

  /**
   * Allows you to add a tester
   */
  public AllRoundTester(Tester testr)
  {
    super(testr.getModel());
    test = testr;
    state = test.addCoverageMetric(new StateCoverage());
    loopTolerance = 1;
  }

  public String getName()
  {
    return "Loop-limited "+test.getName();
  }

  public String getDescription()
  {
    return "This tester limits another tester ("+test.getName()+")" +
    		" so that it goes around loops a maximum number of times" +
    		" (once by default).";
  }

  /**
   *  The maximum number of times that any state can appear
   *  in a test sequence during test generation.
   *  Once this is exceeded, the test sequence is terminated by doing a reset.
   */
  public int getLoopTolerance()
  {
    return loopTolerance;
  }

  /**
   * Lets you set how many times the algorithm will tolerate a loop
   */
  public void setLoopTolerance(int t)
  {
    loopTolerance = t;
  }

  public int allRoundTrips()
  {
    int taken = test.generate();
    if (taken < 0) {
      state.clear();
      // we have done the clear after the reset, so we manually
      // mark the initial state as already visited.
      state.doneReset("User", true);
    }
    else {
      Object curr = test.getModel().getCurrentState();
      Integer count = state.getDetails().get(curr);
      //System.out.println("visited state " + curr + " " + count + " times");
      if (count > getLoopTolerance()) {
        state.clear(); // do clear before reset, so reset covers initial state
        test.getModel().doReset("AllRoundTrips");
      }
    }
    return taken;
  }

  public int generate()
  {
    return this.allRoundTrips();
  }
}
