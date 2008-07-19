/**
 * 
 */
package net.sourceforge.czt.modeljunit.gui.visualisaton;

import org.apache.commons.collections15.Transformer;

import edu.uci.ics.jung.graph.Graph;

/**
 * @author Jerramy Winchester
 *
 */
public class InfoLabelTransformer<v, E> implements Transformer<Object, String>{

	@Override
	public String transform(Object o) {
		if(o instanceof VertexInfo){
			return "   Vertex:   " + ((VertexInfo)o).getName();
		} else if(o instanceof EdgeInfo){
			return "                                Action taken:  " + ((EdgeInfo)o).getAction();
		} else if(o instanceof Graph){
			return "Graph";
		} else {
			return (String)o.toString();
		}
		
	}
	
}
