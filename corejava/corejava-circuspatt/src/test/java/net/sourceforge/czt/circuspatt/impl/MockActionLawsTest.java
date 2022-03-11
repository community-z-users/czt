/*
 * AstTest.java
 *
 * Created on 12 June 2007, 15:01
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.circuspatt.impl;

import java.util.List;
import junit.framework.*;
import net.sourceforge.czt.circus.ast.ActionTransformerPred;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.Model;
import net.sourceforge.czt.circus.ast.Transformation;
import net.sourceforge.czt.circus.ast.TransformerPred;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.zpatt.ast.JokerPred;

/**
 * A (junit) test class which contains a collection of AST tests
 * like calling create methods, validating, etc.
 *
 * @author Petra Malik
 */
public class MockActionLawsTest extends TestCase {
    
    public static Test suite() {
        TestSuite suite = new TestSuite();
        
        suite.addTestSuite(SequentialCompositionUnit1.class);
        return suite;
    }
        
    /**
     * A (junit) test class for AndExpr.
     */
    public static class SequentialCompositionUnit1 extends LawTest {        
        
        public SequentialCompositionUnit1(String name) {
            super(name);
        }
        
        /*
        protected Term createTerm() {            
            //\begin{ActionLaw}{Sequential\_Composition\_Unit\_1}
            //        Skip; A	\refs A
            //\end{ActionLaw}             
            CircusAction spec = factory_.createSeqAction(factory_.createSkipAction(),
                factory_.createJokerAction("A", null));
            CircusAction impl = factory_.createJokerAction("A", null);
            ActionTransformerPred transformer = factory_.createActionTransformerPred(
                null, Transformation.Refinement, Model.FlDv, spec, impl);
            return CircusPattUtils.createCircusLaw(getLawName(),
                transformer, factory_.<Pred>list());
        }
         */
        
        protected String getLawName() {
            return "Sequential_Composition_Unit_1";
        }

        protected TransformerPred createTransformerPred() {
            CircusAction spec = factory_.createSeqAction(factory_.list(factory_.createSkipAction(),
                factory_.createJokerAction("A", null)));
            CircusAction impl = factory_.createJokerAction("A", null);
            ActionTransformerPred transformer = factory_.createActionTransformerPred(
                null, Transformation.Refinement, Model.FlDv, factory_.list(spec, impl));
            return transformer;
        }

        protected List<? extends Pred> createProvisos() {
            return factory_.<Pred>list();
        }
    }
    
    
    /**
     * A (junit) test class for AndExpr.
     */
    public static class GuardIntroductionSchemaExpression extends LawTest {        
        
        public GuardIntroductionSchemaExpression(String name) {
            super(name);
        }
        // The arguments are just global jokers with the given names
        // By the way, SExp should also be an argument (i.e. a Joker).
        /*
        \begin{ActionLaw}{Guard\_Introduction\_Schema\_Expression}
		SExp
	\refs
		(g\_1 \guard SExp)
		\extchoice
		(g\_2 \guard SExp)
	\provided
		\pre(SExp) \implies g\_1
		\next
		\pre(SExp) \implies g\_2
	\args
		\predicate g\_1
		\predicate g\_2
        \end{ActionLaw} 
         */        
        protected String getLawName() {
            return "Guard_Introduction_Schema_Expression";
        }

        protected TransformerPred createTransformerPred() {
            /* NOTE:
             * Fresh instances ought always to be used within Mock classes,
             * since this is the way the parser would create them. Caching 
             * the ASTs is dangerous as aliasing may create tricky side-effects.
             * 
             * That is, one should not reuse the value of createSExpr or createGuard.
             */
            CircusAction spec = createSExprAction();            
            CircusAction impl = factory_.createExtChoiceAction(factory_.list(
                factory_.createGuardedAction(createSExprAction(), createGuard("g1")),
                factory_.createGuardedAction(createSExprAction(), createGuard("g2"))));            
            
            // For simulation or equivalence, see Transformation.
            ActionTransformerPred transformer = factory_.createActionTransformerPred(
                null, Transformation.Refinement, Model.FlDv, 
                factory_.list(spec, impl));
            return transformer;
        }

        protected List<? extends Pred> createProvisos() {
            //\pre(SExp) \implies g\_1
            //\pre(SExp) \implies g\_2
            return factory_.list(
                factory_.createImpliesPred(
                    factory_.createExprPred(factory_.createPreExpr(createSExprJoker())), createGuard("g1")),
                factory_.createImpliesPred(
                    factory_.createExprPred(factory_.createPreExpr(createSExprJoker())), createGuard("g2")));
        }
        
        
        private CircusAction createSExprAction() {
            CircusAction result = factory_.createSchExprAction(createSExprJoker());
            
            /* NOTE:
             * Alternatively, one could create it directly as an
             * action joker and then bind it to the SchExprAction 
             * which SExpr represents.
             * WARNING:
             * This shall becomea parsing ambiguity for the grammar,
             * whenever the parser is implemented.
             */            
            //CircusAction alternative = factory_.createJokerAction("SExpr", null);            
                        
            // NOTE: 
            //     In fact, as you want to use it within the 
            //     proviso as an expression joker, it makes more 
            //     sense to be an expression joker result here.
            //     However, the parsing conflict still remains.                             
            return result;
        }
        
        private Expr createSExprJoker() {
            return factory_.createJokerExpr("SExpr", null);
        }
        
        private JokerPred createGuard(String name) {
            return factory_.createJokerPred(name, null);
        }
    }
    
}
