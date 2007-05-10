/*
 * ZEvesIncompatibleException.java
 *
 * Created on 15 September 2005, 12:41
 */

package net.sourceforge.czt.zeves;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.ast.TermA;
import net.sourceforge.czt.z.ast.LocAnn;

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
    
    public ZEvesIncompatibleException(String headline, Term term) {
        super(createZEvesIncompatibleExceptionMessage(headline, term));
    }
    
    protected static String createZEvesIncompatibleExceptionMessage(String headline, Term term) {        
        String message = "Unknown CZT " + headline + " for Z/Eves translation: " + term.getClass().getName();
        if (term instanceof TermA) {
            LocAnn loc = (LocAnn)((TermA)term).getAnn(LocAnn.class);
            if (loc != null) {
                message += " at " + loc.getLoc() + " (L:" + loc.getLine() + "; C:" + loc.getCol() + ").";
            }
        } else message += ".";
        return message;
    }
}