/**
 * 
 */
package net.sourceforge.czt.modeljunit.gui.visualisaton;

import java.awt.Color;
import java.awt.Paint;
import java.util.ArrayList;

import org.apache.commons.collections15.Transformer;

import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.visualization.picking.PickedInfo;

/**
 * @author Jerramy Winchester
 *
 */
public class VertexEdgePaintTransformer<V,E> implements Transformer<V, Paint> {	
	
	private PickedInfo<Object> pi;
	private ArrayList<Object> vertecies_;
	
	public VertexEdgePaintTransformer(PickedInfo<Object> pi, ArrayList<Object> v){
		if (pi == null)
			throw new IllegalArgumentException("PickedInfo instance must be non-null");
		this.pi = pi;
		this.vertecies_ = v;
	}	
	
	@Override
	public Paint transform(V v){
		
		try{
			if (v instanceof Graph){	
				if(pi.isPicked(v)){
					return Color.RED;
				}				
				return Color.BLACK;						
			}
			if(v instanceof VertexInfo){
				if (pi.isPicked(vertecies_.get(vertecies_.indexOf(v)))){					
					return Color.RED;
				}
				else
				{				
					if(vertecies_.contains(v)){
						VertexInfo vert = (VertexInfo)vertecies_.get(vertecies_.indexOf(v));
						if(vert.getIsDisplayed() || vert.getIsVisited()){							
							return Color.BLACK;
						}
					}
				}
			}							
			return Color.BLACK;
						
		} catch (Exception e){						
			return Color.BLACK;
		}
	}

}
