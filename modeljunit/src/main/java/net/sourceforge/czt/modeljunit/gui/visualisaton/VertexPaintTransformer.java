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

import java.awt.Color;
import java.awt.Paint;
import java.util.ArrayList;

import org.apache.commons.collections15.Transformer;

import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.visualization.picking.PickedInfo;

/**
 * This class is responsible for painting the vertices of a graph the correct colour.
 * @author Jerramy Winchester
 *
 * @param <V>	The vertecies
 * @param <E>	The edges
 */
public class VertexPaintTransformer<V,E> implements Transformer<V, Paint> {	
	
	private PickedInfo<Object> pi;
	private ArrayList<Object> vertecies_;

	public VertexPaintTransformer(PickedInfo<Object> pi, ArrayList<Object> v) {
		if (pi == null)
			throw new IllegalArgumentException("PickedInfo instance must be non-null");
		this.pi = pi;
		this.vertecies_ = v;
	}	

	@Override
	public Paint transform(V v) {
		try{
			if (v instanceof Graph){
				if(pi.isPicked(v)){
					return Color.YELLOW;
				}
				return new Color(45, 155, 32) ;
			}
			if(v instanceof VertexInfo){
				if (pi.isPicked(vertecies_.get(vertecies_.indexOf(v)))){				
					return Color.YELLOW;
				}
				else
				{				
					if(vertecies_.contains(v)){

						VertexInfo vert = (VertexInfo)vertecies_.get(vertecies_.indexOf(v));
						if(vert.getIsDisplayed()){
							return new Color(205, 92, 92) ;
						} else if(vert.getIsVisited()){
							return new Color(255, 192, 203);
						}
					}
				}
			}			
			return new Color(255, 222, 173);
			
			
		} catch (Exception e){			
			return new Color(255, 222, 173);
		}
	}
}

