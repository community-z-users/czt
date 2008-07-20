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
				return str.substring(0, (str.length() <= 20) ? str.length() - 1 : 20).toString() 
											+ (str.length() <= 20 ? "" : "...");
			}			
		} 
		return "";		
	}		
}
