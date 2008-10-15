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
