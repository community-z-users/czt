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

import org.apache.commons.collections15.Transformer;

import edu.uci.ics.jung.graph.Graph;

/**
 * 
 * @author Jerramy Winchester
 *
 * @param <V> The vertices
 * @param <E> The name of the vertex
 */

public class VertexLabelTransformer<V, E> implements Transformer<Object, String>{
	private boolean show_ = true;	
	
	public void setShowLabels(boolean show){
		show_ = show;
	}
	
	@SuppressWarnings("unchecked")
	public String transform(Object o) {		
		if(show_){
			if(o instanceof VertexInfo){
				VertexInfo v = (VertexInfo)o;
				return (String)v.getName();
			}
			if(o instanceof Graph) {
				StringBuffer str = new StringBuffer();
				for(Object i: ((Graph)o).getVertices()){
					if(i instanceof VertexInfo){
						VertexInfo v = (VertexInfo)i;
						str.append(v.getName() + ",");
					}
				}				
				return str.substring(0, (str.length() <= 20) ? ((str.length() - 1) >= 0 ? str.length() - 1 : 0) : 20).toString() 
											+ (str.length() <= 20 ? "" : "...");
			}			
		} 
		return "";		
	}		
}
