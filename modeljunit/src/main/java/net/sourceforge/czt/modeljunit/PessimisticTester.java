/**
 Copyright (C) 2007 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.modeljunit;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Random;

import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.ActionCoverage;

/** An attempt at implementing the Pessimistic Player algorithm
 *
 *  @author Pele Douangsavanh
 */
public class PessimisticTester extends Tester
{
  protected GraphListener graph_;
  protected CoverageMetric transitions_;
	protected CoverageMetric actions_;

  private int depth_;

  private boolean complex_;

  /**
   *  Creates a test generator that can generate random walks.
   *
   * @param model  Must be non-null;
   */
  public PessimisticTester(Model model)
  {
    super(model);
    model.addListener("graph");
    transitions_ = (CoverageMetric) model.addListener(new TransitionCoverage());
		actions_ = (CoverageMetric) model.addListener(new ActionCoverage());
    graph_ = (GraphListener) model.getListener("graph");
    depth_ = 5;
    complex_ = false;
  }

  /**
   * A convenience constructor that puts a Model wrapper around an FsmModel.
   * @param fsm  Must be non-null.
   */
  public PessimisticTester(FsmModel fsm)
  {
    this(new Model(fsm));
  }

  public int evalState(Object state, int depth)
  {
    if (depth == 0)
      return 0;
    int[] worth = new int[model_.getNumActions()];
    
    int result = 0;
    
    return result;
  }

  public int eval(Object state, int action)
  {
    if (complex_ == true)
      return evalComplex(state, action);
    else
      return evalSimple(state, action);
  }

  public int evalSimple(Object state, int action)
  {
		int result = 0;
		Object[] done = new Object[model_.getNumActions()];
		if ((done.length == 0) && ((!(graph_.getTodo(model_.getCurrentState()).get(action)))))
			result += 10;
		else
			result -= done.length;
    return result;
  }

  public int evalComplex(Object state, int action)
  {
		int result = evalSimple(state, action);
		// If state has not been visited and action is in toDo set it gets
		// an even higher bias
		if ((actions_.getDetails().get(state) == 0) && (!(graph_.getTodo(model_.getCurrentState()).get(action))))
			result += 250;
    return result;
  }

  @Override
  public int generate()
  {
    // TODO Auto-generated method stub
    return 0;
  }
}
