/**
Copyright 2007, Leo Freitas
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.z.dc;

/**
 *
 * @author leo
 */
public class Pair<T1, T2> {
    
    public final T1 FIRST;
    public final T2 SECOND;
    
    /** Creates a new instance of NodePair */
    public Pair(T1 e1, T2 e2) {
        if (e1 == null || e2 == null)
            throw new NullPointerException();
        FIRST = e1;
        SECOND = e2;
    }        
    
    public String toString() {        
        return "( " + FIRST + ", " + SECOND + " )";
    }
    
    public String asString() {
        return toString();
    }
    
    public int hashCode() {
        return FIRST.hashCode() + SECOND.hashCode();
    }
    
    public boolean equals(Object o) {
        if (o == null)
            return false;
        else if (o instanceof Pair) {
            Pair<?, ?> p = (Pair<?, ?>)o;
            return (FIRST.equals(p.FIRST) && SECOND.equals(p.SECOND));
        }
        else 
            return false;
    }
}
