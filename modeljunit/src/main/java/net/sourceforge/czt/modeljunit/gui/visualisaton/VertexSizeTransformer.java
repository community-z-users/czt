/**
 * 
 */
package net.sourceforge.czt.modeljunit.gui.visualisaton;

import org.apache.commons.collections15.Transformer;

import edu.uci.ics.jung.graph.Graph;

/**
 * A class that will make vertices larger if they represent
 * a collapsed collection of original vertices
 * @author Tom Nelson
 *
 * @param <V>
 */
class VertexSizeTransformer<V> implements Transformer<V,Integer> {
	int size;
    public VertexSizeTransformer(Integer size) {
        this.size = size;
    }

    public Integer transform(V v) {
        if(v instanceof Graph) {
            return 30;
        }
        return size;
    }
}