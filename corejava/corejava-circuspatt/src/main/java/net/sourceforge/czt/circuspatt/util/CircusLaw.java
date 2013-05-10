/*
 * CircusLaw.java
 *
 * Created on 11 June 2007, 09:01
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.circuspatt.util;

import net.sourceforge.czt.circus.ast.ActionTransformerPred;
import net.sourceforge.czt.circus.ast.ProcessTransformerPred;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.zpatt.ast.Rule;
import net.sourceforge.czt.zpatt.ast.SequentList;
import net.sourceforge.czt.zpatt.impl.RuleImpl;

/**
 * <p>
 * This is a convenience class for a Rule. It provides an interface to
 * access the underlying (general) structure that a Rule offer and can
 * be also used for Circus with the same syntactic category.
 * </p>
 *
 * <p>
 * This class should never be created by the user directly, unless meta-rule
 * application happens on the fly. That is, if there is the need to create
 * new rules as a result of applying an available rule. This class is to be
 * used by the parser only.
 * </p>
 *
 * <p>
 * For proof obligations, one need to look into deduction annotations within the law.
 * </p>
 *
 * @author leo
 */
public final class CircusLaw extends RuleImpl {
    
    /** Creates a new instance of CircusLaw */
    CircusLaw(Rule rule) {
        assert rule != null;
        if (rule == null)
            throw new IllegalArgumentException("Invalid Rule for Circus law.");
        setSequent(rule.getSequent());
        setName(rule.getName());
        setPremisses(rule.getPremisses());        
        getAnns().addAll(rule.getAnns());
    }
    
    /**
     * Accepts a visitor.
     */
    public <R> R accept(net.sourceforge.czt.util.Visitor<R> v) {
        if (v instanceof CircusLawVisitor) {
            CircusLawVisitor<R> visitor = (CircusLawVisitor<R>) v;
            return visitor.visitCircusLaw(this);
        }
        return super.accept(v);
    }
    
    public RuleImpl create(Object[] args) {
        return new CircusLaw(super.create(args));
    }
    
    public boolean isActionLaw() {
        return (getSequent().getPred() instanceof ActionTransformerPred);
    }
    
    public boolean isProcessLaw() {
        return (getSequent().getPred() instanceof ProcessTransformerPred);
    }
    
    /**
     * In a Rule, we have a proviso/side-conditions
     * and a conclusion. Or, if seem as in the sequent
     * calculus, a list of premisses and a conclusion.
     *
     * Sequents are just predicates with some contextual
     * information, which for now is just empty. Sequent
     * may also have deduction annotations associated to
     * them. That determines how that sequent have been
     * transformed.
     *
     * For the LHS/RHS, one just need to query for the
     * Spec/Impl within the transformer predicate.
     */
    public ActionTransformerPred getActionRel() {
        assert isActionLaw();
        // A \subsetsqeq B
        // A \sim B
        // A = B
        return CircusUtils.assertActionTransformerPred(
            getSequent().getPred());
    }
    
    public ProcessTransformerPred getProcessRel() {
        assert isProcessLaw();
        // A \subsetsqeq B
        // A \sim B
        // A = B
        return CircusUtils.assertProcessTransformerPred(
            getSequent().getPred());
    }
    
    /**
     * The provisos are just the Rule's antecedent list.
     * They are sequents (i.e., predicates with context)
     * and it is up to the law's user to decide what to
     * do with such predicates.
     *
     * Some may be automatically discharged, some may be
     * proof obligations that one needs to collect and
     * present to some other tool or to the user.
     */
    public SequentList getProvisoos() {
        return getPremisses();
    }
}


