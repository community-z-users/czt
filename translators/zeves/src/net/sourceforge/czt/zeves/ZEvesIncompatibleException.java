/*
 * ZEvesIncompatibleException.java
 *
 * Created on 15 September 2005, 12:41
 */

package net.sourceforge.czt.zeves;

/**
 * Exception thrown whenever the tool finds a Z Standard term that
 * cannot be converted to Z/Eves Z. For instance, schema boxes with 
 * empty declarations, or declarations of schema-expressions.
 * @author leo
 */
public class ZEvesIncompatibleException extends RuntimeException {
        
    static final long serialVersionUID = -562355333369930614L;
    
    /** Creates a new instance of ZEvesIncompatibleException */
    public ZEvesIncompatibleException(String message) {
        super(message);        
    }
    
    public ZEvesIncompatibleException(String message, Throwable cause) {
        super(message, cause);
    }
    
    public ZEvesIncompatibleException(Throwable cause) {
        super(cause);
    }
}