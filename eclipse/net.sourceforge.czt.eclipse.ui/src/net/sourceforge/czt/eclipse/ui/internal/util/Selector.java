
package net.sourceforge.czt.eclipse.ui.internal.util;

import java.math.BigInteger;
import java.util.Stack;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.ZName;

import org.eclipse.jface.text.Position;

/**
 * @author Chengdong Xu
 */
public class Selector
{
  private Term fAST = null;

  private Stack<Term> fTermStack = new Stack<Term>();

  private int fSelection = -1;

  public Selector(Term ast)
  {
    this.fAST = ast;
  }

  public Term getTerm(Position position)
  {
    init();
    fillTermStack(fAST, position);
    if (fTermStack.isEmpty())
      return null;
//    fSelection = fTermStack.size() - 1;
    fSelection = -1;
    return fTermStack.get(fTermStack.size() - 1);
  }
  
  public Term top()
  {
    if (fTermStack.isEmpty())
      return null;
    return fTermStack.get(fTermStack.size() - 1);
  }

  public Term previous()
  {
    if (fTermStack.isEmpty())
      return null;
    // initial state
    if (fSelection < 0)
      return null;
    fSelection++;
    // reach the top
    if (fSelection == fTermStack.size())
      fSelection--;
    
    return fTermStack.get(fSelection);
  }

  public Term current()
  {
    if (fSelection < 0)
      return null;
    return fTermStack.get(fSelection);
  }

  public Term next()
  {
    if (fTermStack.isEmpty())
      return null;
    // initial state
    if (fSelection < 0)
      fSelection = fTermStack.size() - 1;
    // not reach the bottom
    else if (fSelection > 0)
      fSelection--;
    
    return fTermStack.get(fSelection);
  }

  private void init()
  {
    this.fTermStack.clear();
    this.fSelection = -1;
  }

  private void fillTermStack(Object object, Position position)
  {
    if (object == null || position == null)
      return;
    if (!(object instanceof Term))
      return;
    
    // indicate whether to continue pushing its children
    boolean success = true;
    
    Term term = (Term) object;
    LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
    if (locAnn != null) {
      BigInteger start = locAnn.getStart();
      BigInteger length = locAnn.getLength();
      if ((start != null) && (length != null)) {
        if ((start.intValue() <= position.getOffset())
            && (start.intValue() + length.intValue() >= position.getOffset()
                + position.getLength())) {
          this.fTermStack.push(term);
        }
        else
          success = false;   
      }
    }
    
    if (!success)
      return;
/*    
    if (term instanceof ZRefName)
      return;
*/
    if (term instanceof ZName)
      return;
    
    for (Object child : term.getChildren())
      fillTermStack(child, position);
  }
}
