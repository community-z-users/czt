/*
 * UseCommand.java
 *
 * Created on 16 September 2005, 16:39
 */

package net.sourceforge.czt.zeves.proof;

import net.sourceforge.czt.zeves.ZEvesIncompatibleException;
import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.RenameExpr;

/**
 *
 * @author leo
 */
public class UseCommand extends AbstractProofCommand {
    
    /** Creates a new instance of UseCommand */
    public UseCommand(CZT2ZEvesPrinter zprinter, Expr expr) {
        /* NOTE: Z/Eves uses here theorem-ref production, which in turn 
         *       can be either a RefExpr with decoration and generic actuals,
         *       or a RenameExpr as a RefExpr followed by appropriate replacements.
         */
        super(zprinter, expr);
        if (!(expr instanceof RefExpr || expr instanceof RenameExpr))
            throw new ZEvesIncompatibleException("Use proof command accepts only theorem reference names with replacements. " +
                    "See throwable cause for details.", 
                    new IllegalArgumentException("Z/Eves uses here theorem-ref production, which in turn " +
                        "can be either a RefExpr with decoration and generic actuals, " +
                        "or a RenameExpr as a RefExpr followed by appropriate replacements."));
    }

    protected String format(Object... attrs) {        
        return fZPrinter.print((Expr)attrs[0]);
    }
    
    public ProofCommandType getType() {
        return ProofCommandType.THEOREM_USAGE;
    }

    public String getName() {
        return "use";
    }    
}
