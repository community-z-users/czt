package net.sourceforge.czt.modeljunit.gui.visualisaton;

import net.sourceforge.czt.modeljunit.AbstractListener;
import net.sourceforge.czt.modeljunit.Transition;

/** An implementation of ModelListener that prints
 *  event messages to the Model's <code>getOutput()</code> stream.
 */
public class VisualisationListener extends AbstractListener
{
	private JUNGHelper jView_ = JUNGHelper.getJUNGViewInstance();
	private int resets = 1;

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
		jView_.visitedVertex(tr.getStartState());
		jView_.visitedVertex(tr.getEndState());
		jView_.visitedEdge(tr);
	}

	public void failure(Exception ex)
	{
		System.out.println("FAILURE: "+ex.getLocalizedMessage());
	}
}

