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
        setSizeTransformer(new VertexSizeTransformer<V>(28));
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
