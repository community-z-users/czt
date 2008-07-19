/**
 * 
 */
package net.sourceforge.czt.modeljunit.gui.visualisaton;

import java.awt.Color;
import java.awt.Paint;

import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.decorators.GradientEdgePaintTransformer;
import edu.uci.ics.jung.visualization.picking.PickedInfo;

/**
 * @author Jerramy Winchester
 *
 */
public class EdgePaintTransformer<V, E> extends GradientEdgePaintTransformer<Object, Object> {

	private VisualizationViewer<Object, Object> vv_;

	public EdgePaintTransformer(Color c1, Color c2, VisualizationViewer<Object, Object> vv) {
		super(c1, c2, vv);
		vv_ = vv;				
	}	

	public Paint transform(Object o){

		if(o instanceof EdgeInfo){			
			EdgeInfo e = (EdgeInfo)o;
			PickedInfo<Object> pi = vv_.getPickedEdgeState();
			if(pi.isPicked(o)){
				return Color.RED;
			} else if(e.getIsDisplayed() || e.getIsVisited()){            		
				return Color.BLACK;
			}
		}
		return new Color(180,180,200);
	}    
}
