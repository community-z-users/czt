/*
 * ProofScript.java
 *
 * Created on 16 September 2005, 15:34
 */

package net.sourceforge.czt.zeves.proof;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.zeves.z.BasicZEvesTranslator;
import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;

/**
 *
 * @author leo
 */
public class ProofScript extends BasicZEvesTranslator {
    
    private String fScript;
    private boolean fModified;    
    private final List<ProofCommand> fCmds;
    private final CZT2ZEvesPrinter fZPrinter;    
    
    /** Creates a new instance of ProofScript */
    public ProofScript(CZT2ZEvesPrinter zprinter) {    
        super();
        if (zprinter == null)
            throw new NullPointerException("Invalid CZT to Z/Eves XML converted.");
        fScript = "";
        fModified = false;        
        fCmds = new ArrayList<ProofCommand>(50);        
        fZPrinter = zprinter;
    }
    
    private String buildScript() {
        StringBuilder result = new StringBuilder("");
        if (size() != 0) {
            Iterator<ProofCommand> it = commands();        
            ProofCommand pc = it.next();
            result.append(pc.getCommand());
            while (it.hasNext()) {
                result.append(";\n");            
                pc = it.next();
                result.append(pc.getCommand());
            }        
        }
        return result.toString();
    }    
    
    private String wrapProofCommand(String command) {               
        return format(ZEVES_COMMAND, "proof-command", command);
    }
    
    public int size() {
        return fCmds.size();
    }
    
    public final Iterator<ProofCommand> commands() {
        return Collections.unmodifiableList(fCmds).iterator();
    }
    
    public final List<String> translate() {
        List<String> result = new ArrayList<String>(size());                
        ProofCommand pc;
        Iterator<ProofCommand> it = commands();        
        while (it.hasNext()) {            
            pc = it.next();
            result.add(wrapProofCommand(pc.getCommand()));            
        }                
        return result;
    }
    
    public final String toString() {
        if (fModified) {
            fScript = buildScript();
            fModified = false;
        }
        return fScript;
    }
    
    public void clear() {
        fModified = true;
        fCmds.clear();        
    }
    
    /* PROOF COMMANDS FACTORY METHODS */
    
    /* Case Analysis Proof Commands */
    
    public void addCasesCommand() {
        fModified = fCmds.add(new SimpleCommand("cases", ProofCommandType.CASE_ANALYSIS));
    }
    
    public void addNextCommand() {
        fModified = fCmds.add(new SimpleCommand("next", ProofCommandType.CASE_ANALYSIS));
    }
    
    public void addConjunctiveCommand() {
        fModified = fCmds.add(new SimpleCommand("conjunctive", ProofCommandType.CASE_ANALYSIS));
    }
    
    public void addDisjunctiveCommand() {
        fModified = fCmds.add(new SimpleCommand("disjunctive", ProofCommandType.CASE_ANALYSIS));
    }
    
    public void addSplitCommand(Pred pred) {
        fModified = fCmds.add(new SplitCommand(fZPrinter, pred));
    }
    
    /* Theorem Usage Proof Commands */
    
    public void addApplyCommand(String thmName) {
        fModified = fCmds.add(new ApplyCommand(fZPrinter, thmName));                
    }
    
    public void addApplyCommand(String thmName, Expr expr) {
        fModified = fCmds.add(new ApplyCommand(fZPrinter, thmName, expr));
    }
    
    public void addApplyCommand(String thmName, Pred pred) {
        fModified = fCmds.add(new ApplyCommand(fZPrinter, thmName, pred));
    }
    
    public void addUseCommand(Expr expr) {
        fModified = fCmds.add(new UseCommand(fZPrinter, expr));
    }
    
    public void addInvokeCommand(ZName ref) {
        fModified = fCmds.add(new InvokeCommand(fZPrinter, ref));
    }
    
    public void addInvokeCommand(Pred pred) {
        fModified = fCmds.add(new InvokeCommand(fZPrinter, pred));
    }
    
    /* Equality Proof Command */
    
    public void addEqSubstituteCommand() {
        fModified = fCmds.add(new EqSubstituteCommand());
    }
    
    public void addEqSubstituteCommand(Expr expr) {
        fModified = fCmds.add(new EqSubstituteCommand(fZPrinter, expr));
    }
    
    /* Quantifier Proof Commands */
    
    public void addPrenexCommand() {
        fModified = fCmds.add(new SimpleCommand("prenex", ProofCommandType.QUANTIFIERS));
    }
    
    public void addInstantiateCommand(ZName variable, Expr value) {        
        fModified = fCmds.add(new InstantiateCommand(fZPrinter, variable, value));
    }
    
    public void addInstantiateCommand(ZNameList variables, List<Expr> values) {        
        fModified = fCmds.add(new InstantiateCommand(fZPrinter, variables, values));
    }
    
    /* Reduction Proof Commands */
    
    public void addSimplifyCommand() {
        fModified = fCmds.add(new SimpleCommand("simplify", ProofCommandType.REDUCTION));
    }
     
    public void addRewriteCommand() {
        fModified = fCmds.add(new SimpleCommand("rewrite", ProofCommandType.REDUCTION));
    }
    
    public void addReduceCommand() {
        fModified = fCmds.add(new SimpleCommand("reduce", ProofCommandType.REDUCTION));
    }
    
    public void addProveCommand() {
        fModified = fCmds.add(new SimpleCommand("prove by rewrite", ProofCommandType.REDUCTION));
    }
    
    public void addProveByReduceCommand() {
        fModified = fCmds.add(new SimpleCommand("prove by reduce", ProofCommandType.REDUCTION));
    }
    
    public void addTrivialSimplifyCommand() {
        fModified = fCmds.add(new SimpleCommand("trivial simplify", ProofCommandType.REDUCTION));
    }

    public void addTrivialRewriteCommand() {
        fModified = fCmds.add(new SimpleCommand("trivial rewrite", ProofCommandType.REDUCTION));
    }
    
    public void addRearrangeCommand() {
        fModified = fCmds.add(new SimpleCommand("rearrange", ProofCommandType.REDUCTION));
    }    
    
    /* Modifier Proof Commands */
    
    public void addWithDisabledCommand(ZNameList eventNameList, ProofCommand cmd) {
        /* NOTE: Pass ProofCommand first for a homogeneous format(...) implementation.
         */
        fModified = fCmds.add(new WithCommand("with disabled", fZPrinter, cmd, eventNameList));
    }
    
    public void addWithEnabledCommand(ZNameList eventNameList, ProofCommand cmd) {
        /* NOTE: 
         * 
         * Z/Eves does not allow empty event name lists.
         * However, if one tries a name not declared, the command simply has no effect!
         * Ex: "with enabled (nonExistingEventName) reduce", the prover goes nowhere, obviously.
         */
        if (eventNameList.isEmpty())
            throw new IllegalArgumentException("Event name list cannot be empty");
        fModified = fCmds.add(new WithCommand("with enabled", fZPrinter, cmd, eventNameList));
    }
    
    public void addWithExpressionCommand(Expr expr, ProofCommand cmd) {
        fModified = fCmds.add(new WithCommand("with expression", fZPrinter, cmd, expr));
    }
    
    public void addWithPredicateCommand(Pred pred, ProofCommand cmd) {
        fModified = fCmds.add(new WithCommand("with predicate", fZPrinter, cmd, pred));
    }

    public void addWithNormalizationCommand(ProofCommand cmd) {
        fModified = fCmds.add(new WithCommand("with normalization", fZPrinter, cmd));
    }    
}
