/*
 * WithCommand.java
 *
 * Created on 16 September 2005, 17:24
 */

package net.sourceforge.czt.zeves.proof;

import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;
import java.util.List;
import java.util.Iterator;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZName;

/**
 *
 * @author leo
 */
public class WithCommand extends SimpleCommand {   
    
    /** Creates a new instance of WithCommand */
    WithCommand(String name, CZT2ZEvesPrinter zprinter, Object... attrs) {
        super(name, ProofCommandType.MODIFIERS, zprinter, attrs);
    } 
    
    protected String format(Object... attrs) {
        assert attrs != null && attrs.length > 0;
        String result;
        // Mandatory command
        String command = ((ProofCommand)attrs[0]).getCommand();        
        if (attrs.length == 1)
            result = command;
        else {
            String other;
            if (attrs[1] instanceof Expr || attrs[1] instanceof Pred)
                other = fZPrinter.print((Term)attrs[1]);
            else {
                StringBuilder evtList = new StringBuilder();
                assert !((ZNameList)attrs[1]).isEmpty();
                Iterator<Name> it = ((ZNameList)attrs[1]).iterator();
                ZName rname = ZUtils.assertZName(it.next());                 // guaranteed to have at least one.
                evtList.append(fZPrinter.print(rname));
                while (it.hasNext()) {
                    evtList.append(", ");
                    rname = ZUtils.assertZName(it.next());                
                    evtList.append(fZPrinter.print(rname));
                }
                other = evtList.toString();
            }            
            result = " (" + other + ") " + command;
        }        
        return result;
    }
}
