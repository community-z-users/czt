/**
 * 
 */
package net.sourceforge.czt.modeljunit.gui.visualisaton;

import java.awt.BasicStroke;
import java.awt.Stroke;

import org.apache.commons.collections15.Transformer;

/**
 * @author Jerramy Winchester
 *
 */
public class EdgeStrokeTransformer<V,E> implements Transformer<Object, Stroke> {

	//Set the lines that the graph should use between vertecies
	private float dash[] = {5.0f};
	private final Stroke edgeStroke = new BasicStroke(1.0f, BasicStroke.CAP_BUTT,
			BasicStroke.JOIN_MITER, 10.0f, dash, 0.0f);

	/**
	 * Return the stroke for this edge.
	 */
	public Stroke transform(Object o) {	
		if(o instanceof EdgeInfo){
			EdgeInfo e = (EdgeInfo)o;
			if(e.getIsDisplayed()){            		
				return new BasicStroke(2.0f);
			}else{
				if(e.getIsVisited()){
					return new BasicStroke(0.45f);
				}
			}
		}
		return edgeStroke;
	} 
}
