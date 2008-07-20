/**
 * 
 */
package net.sourceforge.czt.modeljunit.gui.visualisaton;

import java.awt.Shape;

import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.visualization.decorators.EllipseVertexShapeTransformer;

/**
 * a class that will create a vertex shape that is either a
 * polygon or star. The number of sides corresponds to the number
 * of vertices that were collapsed into the vertex represented by
 * this shape.
 * 
 * @author Tom Nelson
 *
 * @param <V>
 */
class VertexShapeTransformer<V> extends EllipseVertexShapeTransformer<V> {

    VertexShapeTransformer() {
        setSizeTransformer(new VertexSizeTransformer<V>(25));
    }
    @Override
    public Shape transform(V v) {
        if(v instanceof Graph) {
        	/*
            int size = ((Graph)v).getVertexCount();
            if (size < 8) {   
                int sides = Math.max(size, 3);
                return factory.getRegularPolygon(v, sides);
            }
            else {
                return factory.getRegularStar(v, size);
            }
            */
        	return factory.getRoundRectangle(v);
        	
        }
        return super.transform(v);
    }
}
