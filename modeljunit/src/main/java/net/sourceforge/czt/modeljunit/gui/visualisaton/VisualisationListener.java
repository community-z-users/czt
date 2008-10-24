/**
 Copyright (C) 2008 Jerramy Winchester
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License as published
 by the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.modeljunit.gui.visualisaton;

import net.sourceforge.czt.modeljunit.AbstractListener;
import net.sourceforge.czt.modeljunit.TestFailureException;
import net.sourceforge.czt.modeljunit.Transition;

/** 
 * An implementation of ModelListener that passes information about the model
 * to the JUNGHelper class.
 */
public class VisualisationListener extends AbstractListener
{
	private JUNGHelper jView_ = JUNGHelper.getJUNGViewInstance();
	private int resets = 1;
	private Boolean failureOccured = false;
	private Object lastVisitedState_;
	private Transition lastVisitedTrans_;
	private String lastVisitedFailedMsg_;


	public VisualisationListener(){
	}

	public String getName()
	{
		return "visualGraph";
	}

	public void doneReset(String reason, boolean testing)
	{ 		
		jView_.graphDoneReset("Test sequence " + (++resets) + " (" + reason + " reset)");		
	}

	public void doneGuard(Object state, int action, boolean enabled, int value)
	{
	}

	public void startAction(Object state, int action, String name)
	{
	}

	public void doneTransition(int action, Transition tr)
	{ 		
		//Tidy up any errored states.
		if(!tr.getStartState().equals(lastVisitedState_) 
				&& null != lastVisitedState_
				&& failureOccured){			
			jView_.visitedEdge(lastVisitedTrans_, true, lastVisitedFailedMsg_);			
		} else {
			jView_.visitedVertex(tr.getStartState(), false);
			jView_.visitedVertex(tr.getEndState(), false);
			jView_.visitedEdge(tr, failureOccured, lastVisitedFailedMsg_);			
		}
		failureOccured = false;
		lastVisitedFailedMsg_ = null;
	}

	@Override
	public void failure(TestFailureException ex)
	{		
		TestFailureException exp = (TestFailureException)ex;		
		Transition tran = new Transition(exp.getState()
				, exp.getActionName()
				, exp.getState() + "_Fail");		
		lastVisitedState_ = exp.getState();
		lastVisitedTrans_ = tran;
		lastVisitedFailedMsg_ = exp.getLocalizedMessage();
		failureOccured = true;		
	}
}

