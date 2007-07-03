/*
 * InstantiateCommand.java
 *
 * Created on 29 November 2005, 16:01
 * 
 */

package net.sourceforge.czt.zeves.proof;

import java.util.ArrayList;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;

/**
 *
 * @author leo
 */
public class InstantiateCommand  extends AbstractProofCommand {
    
    InstantiateCommand(CZT2ZEvesPrinter zprinter, ZName variable, Expr value) {
        super(zprinter, variable, value);
    }
    
    InstantiateCommand(CZT2ZEvesPrinter zprinter, ZNameList variable, List<Expr> value) {
        super(zprinter, combine(variable, value));
    }
    
    private static Object[] combine(ZNameList variables, List<Expr> values) {
        if (variables == null || values == null)
            throw new NullPointerException("Invalid instantiation command parameters.");        
        if (variables.size() != values.size())
            throw new IllegalArgumentException("The number of variables does not correspond to the number of expressions.");
        if (variables.size() == 0)
            throw new IllegalArgumentException("Instantiate command requires at least one variable name and corresponding expression.");
        List<Term> result = new ArrayList<Term>(variables.size()*2);
        for(int i = 0; i < variables.size(); i++) {
            result.add(variables.get(i));
            result.add(values.get(i));
        }
        return result.toArray();
    }
    
    protected String format(Object... attrs) {
        // Mandatory theorem-name
        assert attrs != null && attrs.length > 1 : "invalid attributes for instantiate command(1)";        
        assert attrs.length / 2 == 0 : "invalid attributes for instantiate command(2)";        
        StringBuilder result = new StringBuilder();
        result.append(fZPrinter.print((Term)attrs[0]));
        result.append(" == ");
        result.append(fZPrinter.print((Term)attrs[1]));
        int i = 2;
        while (i < attrs.length-1) {
            result.append(", ");
            result.append(fZPrinter.print((ZName)attrs[i]));
            result.append(" == ");
            result.append(fZPrinter.print((Expr)attrs[i+1]));
            i += 2;
        }        
        return result.toString();
    }
    
    public ProofCommandType getType() {
        return ProofCommandType.QUANTIFIERS;
    }

    public String getName() {
        return "instantiate";
    }    
}
