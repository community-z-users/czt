/*
 * ZEvesEmptyOutput.java
 *
 * Created on 21 September 2005, 14:35
 */

package net.sourceforge.czt.zeves.response;

/**
 *
 * @author leo
 */
public class ZEvesEmptyOutput extends AbstractZEvesOutput<String> {
    
    /** Creates a new instance of ZEvesEmptyOutput */
    public ZEvesEmptyOutput() {
    }
    
    public String getOutput() {
        return "";
    }
    
}
