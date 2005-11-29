/*
 * ZEvesBooleanOutput.java
 *
 * Created on 21 September 2005, 14:36
 */

package net.sourceforge.czt.zeves.response;

/**
 *
 * @author leo
 */
public class ZEvesBooleanOutput extends AbstractZEvesOutput {
    
    private final Boolean fResult;
    
    /** Creates a new instance of ZEvesBooleanOutput */
    public ZEvesBooleanOutput(boolean result) {
        fResult = result;
    }    
    
    public Object getOutput() {
        return fResult;
    }   
    
    protected String getOutputAsString() {
        return "<name ident=\"" + String.valueOf(getOutput()) + "\"/>";
    }
}
