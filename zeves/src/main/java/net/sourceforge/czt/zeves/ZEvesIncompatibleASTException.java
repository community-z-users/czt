/*
 * ZEvesIncompatibleASTException.java
 *
 * Created on 15 September 2005, 12:41
 */

package net.sourceforge.czt.zeves;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.LocAnn;

/**
 * Exception thrown whenever the tool finds a Z Standard term that
 * cannot be converted to Z/EVES Z. For instance, schema boxes with 
 * empty declarations, or declarations of schema-expressions.
 * @author leo
 */
public class ZEvesIncompatibleASTException extends net.sourceforge.czt.util.CztException {
        
    static final long serialVersionUID = -562355333369930614L;
    
    /**
   * Creates a new instance of ZEvesIncompatibleASTException
   */
    public ZEvesIncompatibleASTException(String message) {
        super(message);        
    }
    
    public ZEvesIncompatibleASTException(String message, Throwable cause) {
        super(message, cause);
    }
    
    public ZEvesIncompatibleASTException(Throwable cause) {
        super(cause);
    }
    
    public ZEvesIncompatibleASTException(String headline, Term term) {
        super(createZEvesIncompatibleExceptionMessage(headline, term));
    }
    
    protected static String createZEvesIncompatibleExceptionMessage(String headline, Term term) {        
        String message = "Unknown CZT " + headline + " for Z/EVES translation: " + term.getClass().getName();        
        LocAnn loc = (LocAnn)((Term)term).getAnn(LocAnn.class);
        if (loc != null) {
            message += " at " + loc.getLoc() + " (L:" + loc.getLine() + "; C:" + loc.getCol() + ")";
        }
        message += ".";
        return message;
    }
}
