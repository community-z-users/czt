package net.sourceforge.czt.modeljunit.gui.visualisaton;

import org.apache.commons.collections15.Predicate;

import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.util.Context;

public class EdgeDisplayPredicate<V,E> implements Predicate<Context<Graph<V,E>,E>>
{
	protected boolean show_;
	protected final static int MIN_DEGREE = 1;

	public EdgeDisplayPredicate(boolean filter)
	{
		this.show_ = filter;
	}

	public void showExplored(boolean b)
	{
		show_ = b;
	}

	public boolean evaluate(Context<Graph<V,E>,E> context) {		
		E e = context.element;
		
		if (show_){			
			if(e instanceof EdgeInfo){
				EdgeInfo edge = (EdgeInfo)e;
				return edge.getIsVisited();
			}
			return true;
		} else {
			return true;
		}
	}
}