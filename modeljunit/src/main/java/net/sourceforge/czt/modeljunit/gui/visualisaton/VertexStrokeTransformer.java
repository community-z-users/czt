package net.sourceforge.czt.modeljunit.gui.visualisaton;

import java.awt.BasicStroke;
import java.awt.Stroke;

import org.apache.commons.collections15.Transformer;

import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.visualization.picking.PickedInfo;

public class VertexStrokeTransformer<V, E> implements Transformer<V, Stroke>{

	protected boolean highlight = true;
	protected Stroke heavy = new BasicStroke(2);
	protected Stroke medium = new BasicStroke(1.8f);
	protected Stroke light = new BasicStroke(0.8f);
	protected PickedInfo<V> pi;
	protected Graph<V,E> graph;

	public VertexStrokeTransformer(Graph<V,E> graph, PickedInfo<V> pi)
	{
		this.graph = graph;
		this.pi = pi;
	}

	public void setHighlight(boolean highlight)
	{
		this.highlight = highlight;
	}


	public Stroke transform(V v)
	{
		if (highlight)
		{
			if(v instanceof VertexInfo){
				if (pi.isPicked(v)){				
					return heavy;
				}
				else
				{					
					try{
						for(V w : graph.getNeighbors(v)){
							if (pi.isPicked(w))
								return medium;
						}
					} catch(Exception ex){
						//Ignore
					}
				}
			}
		}		
		return light; 
	}
}
