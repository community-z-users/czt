/*
 * NodePair.java
 *
 * Created on 07 March 2005, 14:45
 */
package net.sourceforge.czt.util;

/*
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
    
    public T1 getFirst()
    {
       return FIRST;
    }

    public T2 getSecond() {
       return SECOND;
    }
}
