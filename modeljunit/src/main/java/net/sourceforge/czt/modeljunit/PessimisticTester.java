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

/** An attempt at implementing the Pessimistic Player algorithm
 *
 *  @author Pele Douangsavanh
 */
 public class PessimisticTester extends Tester
 {
	 protected GraphListener graph_;
	 
	 private int depth;
	 
	 private boolean complex;
	 
	 /**
   *  Creates a test generator that can generate random walks.
   *
   * @param model  Must be non-null;
   */
  public PessimisticTester(Model model)
  {
    super(model);
    model.addListener("graph");
    graph_ = (GraphListener) model.getListener("graph");
		depth = 5;
		complex = false;
  }

  /**
   * A convenience constructor that puts a Model wrapper around an FsmModel.
   * @param fsm  Must be non-null.
   */
  public PessimisticTester(FsmModel fsm)
  {
    this(new Model(fsm));
  }
	
	public int player(Object state, int depth)
	{
		if(depth == 0)
		{
			return 0;
		}
		// Store largest transition value pair
		// Return the best value
	}
	
	public int eval(Object transition)
	{
		if(complex == true)
			return evalComplex(transition);
		else
			return evalSimple(transition);
	}
	
	public int evalSimple(Object transition)
	{
		
	}
	
	public int evalComplex(Object transition)
	{
		
	}
	
	public int mem(Object transition)
	{
	}
 }