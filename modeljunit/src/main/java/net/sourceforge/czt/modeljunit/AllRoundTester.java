package net.sourceforge.czt.modeljunit;

import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;

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
    test.addCoverageMetric(state);
    loopTolerance = 1;
  }

  /**
   * A convenience constructor that puts a Model wrapper around an FsmModel.
   * @param fsm  Must be non-null.
   */
  public AllRoundTester(FsmModel fsm)
  {
    this(new Model(fsm));
    test = new GreedyTester(model_);
    state = new StateCoverage();
    test.addCoverageMetric(state);
    loopTolerance = 1;
  }
  
  public AllRoundTester(Tester testr)
  {
	  super(testr.getModel());
	  test = testr;
	  state = new StateCoverage();
	  test.addCoverageMetric(state);
	  loopTolerance = 1;
  }

  public int getLoopTolerance() {
	  return loopTolerance;
  }
  
  public void setLoopTolerance(int t) {
	  loopTolerance = t;
  }
  
  /** Uses a greedy random walk to try and test all loops in the model.
   *
   * @param maxLength  The number of test steps to do.
   * @param rand       The random number generator used to choose paths.
   */
  public int allRoundTrips()
  {
    int taken = test.generate();
    if (taken < 0) {
        System.out.println("reset state coverage");
        state.clear();
    }
    else 
    {
        if (state.getDetails().get(test.getModel().getCurrentState()) > getLoopTolerance()) {
          test.reset();
          state.clear();
        }
    }
    return taken;
  }
  
  public int generate()
  {
	  return this.allRoundTrips();
  }
}
