package net.sourceforge.czt.eclipse.ui.internal.outline;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;

/**
 * A visitor that delegates responsibility of producing results in sequence
 * to its internal visitors. If first visitor fails to produce a result (returns null),
 * the responsibility falls onto the next one.
 * 
 * @author Andrius Velykis
 */
public class ChainTermVisitor<R> implements TermVisitor<R>
{
  private final List<TermVisitor<R>> visitors = new ArrayList<TermVisitor<R>>();
  
  public ChainTermVisitor(List<TermVisitor<R>> visitors) {
    this.visitors.addAll(visitors);
  }
  
  @Override
  public R visitTerm(Term term)
  {
    
    for (TermVisitor<R> visitor : visitors) {
      
      R result = term.accept(visitor);
      if (result != null) {
        return result;
      }
    }
    
    return null;
  }

}
