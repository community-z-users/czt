/**
 * 
 */
package net.sourceforge.czt.modeljunit.gui.visualisaton;
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
				return Color.blue;
			} else if(e.getFailedEdge()){
				return Color.red;
			} else if(e.getIsDisplayed() || e.getIsVisited()){            		
				return Color.black;
			}
		}
		return new Color(140,140,200);
	}    
}
