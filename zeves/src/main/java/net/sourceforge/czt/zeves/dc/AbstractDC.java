/*
 * AbstractDC.java
 *
 * Created on 03 July 2007, 03:28
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.zeves.dc;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.zeves.ZEvesIncompatibleASTException;

/**
 *
 * @author leo
 */
public abstract class AbstractDC implements TermVisitor<Pred>
{
  
  /** Creates a new instance of AbstractDC */
  public AbstractDC()
  {
  }

  public Pred visitTerm(Term zedObject)
  {
    throw new ZEvesIncompatibleASTException("Could not calculate domain check for term " + zedObject);
  }
  
}
