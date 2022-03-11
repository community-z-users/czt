/*
 * ZEvesServerConnectionException.java
 *
 * Created on 19 September 2005, 12:15
 */

package net.sourceforge.czt.zeves;

/**
 * 
 * @author leo
 * @deprecated part of obsoleted {@link ZEvesSocket} implementation
 * @see ZEvesException
 */
@Deprecated
public class ZEvesServerConnectionException extends Exception {
    
    static final long serialVersionUID = -7830153568452854242L;
    
    /** Creates a new instance of ZEvesIncompatibleException */
    public ZEvesServerConnectionException(String message) {
        super(message);        
    }
    
    public ZEvesServerConnectionException(String message, Throwable cause) {
        super(message, cause);
    }
    
    public ZEvesServerConnectionException(Throwable cause) {
        super(cause);
    }
    
}
