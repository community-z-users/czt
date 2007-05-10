/*
 * EqSubstituteCommand.java
 *
 * Created on 16 September 2005, 16:55
 */

package net.sourceforge.czt.zeves.proof;

import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;
import net.sourceforge.czt.z.ast.Expr;

/**
 *
 * @author leo
 */
public class EqSubstituteCommand extends AbstractProofCommand {
    
    /** Creates a new instance of EqSubstituteCommand */
    EqSubstituteCommand() {
        super();
    }
    
    EqSubstituteCommand(CZT2ZEvesPrinter zprinter, Expr expr) {
        super(zprinter, expr);
    }    
    
    protected String format(Object... attrs) {
        String result;
        if (attrs == null || attrs.length == 0)
            result = "";
        else if (attrs[0] instanceof Expr)
            result = fZPrinter.print((Expr)attrs[0]);
        else 
            throw new IllegalArgumentException("Invalid attribute for Equality Substitute proof command: " + String.valueOf(attrs[0]));        
        return result;
    }

    public ProofCommandType getType() {
        return ProofCommandType.EQUALITIES;
    }

    public String getName() {
        return "equality substitute";
    }
}
