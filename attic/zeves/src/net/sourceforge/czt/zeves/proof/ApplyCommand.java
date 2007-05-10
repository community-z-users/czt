/*
 * ApplyCommand.java
 *
 * Created on 16 September 2005, 15:56
 */

package net.sourceforge.czt.zeves.proof;

import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;
import net.sourceforge.czt.base.ast.TermA;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;

/**
 *
 * @author leo
 */
public class ApplyCommand extends AbstractProofCommand {
    
    /** Creates a new instance of ApplyCommand */
    ApplyCommand(CZT2ZEvesPrinter zprinter, String thmName) {
        super(zprinter, thmName);
    }
    
    ApplyCommand(CZT2ZEvesPrinter zprinter, String thmName, Expr expr) {
        super(zprinter, thmName, expr);
    }
    
    ApplyCommand(CZT2ZEvesPrinter zprinter, String thmName, Pred pred) {
        super(zprinter, thmName, pred);
    }        
    
    protected String format(Object... attrs) {
        // Mandatory theorem-name
        StringBuilder result = new StringBuilder(attrs[0].toString());
        if (attrs.length > 1) {
            result.append(" to ");          
            if (attrs[1] instanceof Expr)
                result.append("expression ");
            else if (attrs[1] instanceof Pred)
                result.append("predicate ");
            else
                throw new IllegalArgumentException("Invalid attribute for Apply proof command: " + String.valueOf(attrs[1]));        
            result.append(fZPrinter.print((TermA)attrs[1]));
        }
        return result.toString();
    }
    
    public ProofCommandType getType() {
        return ProofCommandType.THEOREM_USAGE;
    }

    public String getName() {
        return "apply";
    }    
}
