package net.sourceforge.czt.modeljunit.gui.visualisaton;

import org.apache.commons.collections15.Predicate;

import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.util.Context;

public class VertexDisplayPredicate<V,E> implements Predicate<Context<Graph<V,E>,V>>
{
	protected boolean show_;
	protected final static int MIN_DEGREE = 1;

	public VertexDisplayPredicate(boolean filter)
	{
		this.show_ = filter;
	}

	public void showExplored(boolean b)
	{
		show_ = b;
	}

	public boolean evaluate(Context<Graph<V,E>,V> context) {		
		V v = context.element;
		
		if (show_){			
			if(v instanceof VertexInfo){
				VertexInfo vert = (VertexInfo)v;
				return vert.getIsVisited();
			}
			return true;
		} else {
			return true;
		}
	}
}
