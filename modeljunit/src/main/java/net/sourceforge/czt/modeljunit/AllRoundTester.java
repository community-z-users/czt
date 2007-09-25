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
   *  Creates a test generator that can generate random walks.
   *
   * @param model  Must be non-null;
   */
  public AllRoundTester(Model model)
  {
    super(model);
    test = new GreedyTester(model_);
    state = new StateCoverage();
    test.addListener(state);
    loopTolerance = 1;
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
   *
   */
  public AllRoundTester(Tester testr)
  {
    super(testr.getModel());
    test = testr;
    state = test.addCoverageMetric(new StateCoverage());
    loopTolerance = 1;
  }

  /**
   * Lets you get how many times the algorithm will tolerate a loop
   */
  public int getLoopTolerance() {
	  return loopTolerance;
  }
  
  /**
   * Lets you set how many times the algorithm will tolerate a loop
   */
  public void setLoopTolerance(int t) {
	  loopTolerance = t;
  }
  
  /** Uses a greedy random walk to try and test all loops in the model.
   *
   * @param maxLength  The number of test steps to do.
   * @param rand       The random number generator used to choose paths.
   */

  public void setRandom(Random rand)
  {
    test.setRandom(rand);
  }

  public int allRoundTrips()
  {
    int taken = test.generate();
    if (taken < 0) {
        System.out.println("reset state coverage");
        state.clear();
    }
    else 
    {
      Object curr = test.getModel().getCurrentState();
      assert state != null;
      assert state.getDetails() != null;
      Integer count = state.getDetails().get(curr);
      System.out.println("visited state "+curr+" "
          + state.getDetails().get(curr) + " times");
        if (count > getLoopTolerance()) {
          test.reset();
          state.clear();
          System.out.println("terminated test because we saw state "+curr
              +" "+count+" times.");
        }
    }
    return taken;
  }
  
  public int generate()
  {
	  return this.allRoundTrips();
  }
}
