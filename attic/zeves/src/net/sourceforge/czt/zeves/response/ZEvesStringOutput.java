/*
 * ZEvesStringOutput.java
 *
 * Created on 21 September 2005, 14:36
 */

package net.sourceforge.czt.zeves.response;

/**
 *
 * @author leo
 */
public class ZEvesStringOutput extends AbstractZEvesOutput<String> {
    
    private final String fString;
    
    /** Creates a new instance of ZEvesStringOutput */
    public ZEvesStringOutput(String str) {
        if (str == null || str.equals(""))
            throw new IllegalArgumentException("Invalid String for Z/Eves response.");
        fString = str;
    }
    
    public String getOutput() {
        return fString;
    }
}
