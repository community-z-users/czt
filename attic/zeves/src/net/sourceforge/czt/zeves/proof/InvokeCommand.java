/*
 * InvokeCommand.java
 *
 * Created on 16 September 2005, 16:44
 */

package net.sourceforge.czt.zeves.proof;

import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefName;

/**
 *
 * @author leo
 */
public class InvokeCommand extends AbstractProofCommand {
    
    /** Creates a new instance of InvokeCommand */
    InvokeCommand(CZT2ZEvesPrinter zprinter, RefName ref) {
        super(zprinter, ref);
    }
    
    InvokeCommand(CZT2ZEvesPrinter zprinter, Pred pred) {
        super(zprinter, pred);
    }
    
    protected String format(Object... attrs) {
        String result;
        if (attrs[0] instanceof RefName)
            result = fZPrinter.print((RefName)attrs[0]);
        else if (attrs[0] instanceof Pred)
            result = "predicate " + fZPrinter.print((Pred)attrs[0]);
        else
            throw new IllegalArgumentException("Invalid attribute for Invoke proof command: " + String.valueOf(attrs[0]));        
        return result;
    }

    public ProofCommandType getType() {
        return ProofCommandType.THEOREM_USAGE;
    }

    public String getName() {
        return "invoke";
    }    
}
