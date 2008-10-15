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