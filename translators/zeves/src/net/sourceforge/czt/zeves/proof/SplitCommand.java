/*
 * SplitCommand.java
 *
 * Created on 16 September 2005, 16:37
 */

package net.sourceforge.czt.zeves.proof;

import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;
import net.sourceforge.czt.z.ast.Pred;

/**
 *
 * @author leo
 */
public class SplitCommand extends AbstractProofCommand {
    
    /** Creates a new instance of SplitCommand */
    SplitCommand(CZT2ZEvesPrinter zprinter, Pred pred) {
        // no validation is needed.
        super(zprinter, pred);
    }

    protected String format(Object... attrs) {        
        return fZPrinter.print((Pred)attrs[0]);
    }
    
    public ProofCommandType getType() {
        return ProofCommandType.CASE_ANALYSIS;
    }

    public String getName() {
        return "split";
    }    
}
