/*
 * ZEvesOutput.java
 *
 * Created on 21 September 2005, 14:35
 */

package net.sourceforge.czt.zeves.response;

/**
 *
 * @author leo
 */
public interface ZEvesOutput<T> {
    
    public T getOutput();
    public String toString();    
}
