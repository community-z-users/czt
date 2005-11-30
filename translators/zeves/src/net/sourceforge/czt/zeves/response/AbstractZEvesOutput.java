/*
 * AbstractZEvesOutput.java
 *
 * Created on 26 September 2005, 10:00
 */

package net.sourceforge.czt.zeves.response;

/**
 *
 * @author leo
 */
public abstract class AbstractZEvesOutput<T> implements ZEvesOutput<T> {
    
    /** Creates a new instance of AbstractZEvesOutput */
    public AbstractZEvesOutput() {
    }
    
    public final String toString() {
        return "<zoutput>" + getOutputAsString() + "</zoutput>";
    }    
    
    protected String getOutputAsString() {
        return String.valueOf(getOutput());
    }
}
