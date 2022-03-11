/*
 * CircusUtils.java
 *
 * Created on 15 June 2006, 09:04
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.circuspatt.util;

import java.util.List;
import net.sourceforge.czt.circus.ast.TransformerPred;
import net.sourceforge.czt.circuspatt.ast.CircusJokerType;
import net.sourceforge.czt.circuspatt.ast.CircusJokers;
import net.sourceforge.czt.z.ast.Pred;

import net.sourceforge.czt.zpatt.ast.JokerType;
import net.sourceforge.czt.zpatt.ast.Jokers;
import net.sourceforge.czt.zpatt.ast.Sequent;
import net.sourceforge.czt.zpatt.ast.SequentContext;
import net.sourceforge.czt.zpatt.ast.SequentList;

/**
 *
 * @author leo
 */
public final class CircusPattUtils {
  
  private static final Factory factory_ = new Factory();
  private static final SequentContext NO_SEQCTX = factory_.createSequentContext();
    
  /**
   * Do not create instances of this class.
   */
  private CircusPattUtils() {
  }     
  
  /**
   * Convenience method encapsulating a predicate as sequent without context.
   */
  public static Sequent createSequent(Pred pred) {
      return factory_.createSequent(NO_SEQCTX, pred);
  }  
    
  /**
   * Convenience method encapsulating a list of predicates representing
   * provisos from a law into a sequent list without context.
   */
  public static SequentList createProvisos(List<? extends Pred> provisos) {
     SequentList antecedents = factory_.createSequentList(); 
     for (Pred p : provisos) {
         antecedents.getSequent().add(createSequent(p));
     }
     return antecedents;
  }
  
  /**
   * Mock method for creating zed jokers paragraph. See zpatt LaTeEx examples
   */
  public static Jokers createZedJokers(JokerType kind, List<String> jokers) {
      return factory_.createJokers(jokers, kind);
  }
  
  /**
   * Mock method for creating circus jokers paragraph. Similar as zpatt, see CircusJokerType.
   */  
  public static CircusJokers createCircusJokers(CircusJokerType kind, List<String> jokers) {
      return factory_.createCircusJokers(jokers, kind);
  }
  
  /**
   * <p>
   * Mock method for creating a Circus law from its parts. 
   * </p>
   * <p>
   * It creates a CircusLaw bridge for a Rule AST representing it, given a name,
   * a conclusion as a transformer predicate, and a list of provisos. The law 
   * arguments are (global) jokers paragrph. These paragraphs collect joker names
   * of a certain kind, being them circus or z joker types.
   * </p>
   * <p>
   * The transformer predicate instance determines if this is an action or
   * a process law, as well as which kind of relation the transformation is
   * representing. For deductions (or proof obligations), one 
   * </p>
   * <p>
   * For now, this is  a mock method to create laws, which should
   * eventually be created accordingly using the CircusPattern parser.
   * </p>
   */
  public static CircusLaw createCircusLaw(String name, 
      TransformerPred transformer, List<? extends Pred> provisos) {
      assert name != null && !name.isEmpty() && transformer != null && provisos != null;
      Sequent conclusion = createSequent(transformer);
      return new CircusLaw(factory_.createRule(conclusion, name, createProvisos(provisos)));
  }
}
