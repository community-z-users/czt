/*
 * BasicZEvesTranslator.java
 *
 * Created on 29 November 2005, 17:39
 *
 * To change this template, choose Tools | Options and locate the template under
 * the Source Creation and Management node. Right-click the template and choose
 * Open. You can then make changes to the template in the Source Editor.
 */

package net.sourceforge.czt.zeves.z;

import java.text.MessageFormat;

/**
 *
 * @author leo
 */
public abstract class BasicZEvesTranslator implements ZEvesXMLPatterns {
    
    /**
     * General message format used for various Z/EVES "XML" formatting.
     */
    private final MessageFormat fZEvesXMLFmt;    
    
    /**
     * Creates a new instance of BasicZEvesTranslator 
     */
    protected BasicZEvesTranslator() {
        fZEvesXMLFmt = new MessageFormat("");        
    }
    
    /**
     * Sets the formatting pattern for the underlying MessageFormat object.
     * This method is usually called right before method format.
     * To avoid interference by nested calls, this method should be called
     * right before the format argument.
     *
    private void setZEvesXMLPattern(String pattern) {
        fZEvesXMLFmt.applyPattern(pattern);
    }
    */
    
    /**
     * Applies the format operation from the underlying MessageFormat object
     * set to the last pattern. See constructor for the first pattern.
     * This method is usually called straight after method setZEvesXMLPattern.
     * @param pattern
     * @param arguments
     * @return 
     */
    protected String format(String pattern, Object... arguments) {
        fZEvesXMLFmt.applyPattern(pattern);
        return fZEvesXMLFmt.format(arguments, new StringBuffer(), null).toString();
    }    
}
