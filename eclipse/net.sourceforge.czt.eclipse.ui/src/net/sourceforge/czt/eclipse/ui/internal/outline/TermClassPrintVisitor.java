package net.sourceforge.czt.eclipse.ui.internal.outline;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;

/**
 * A simple term print visitor that outputs term's class. The method
 * also truncates "Impl" suffixes if they exist.
 * 
 * @author Andrius Velykis
 */
public class TermClassPrintVisitor implements TermVisitor<String>
{

  @Override
  public String visitTerm(Term term)
  {
    String classname = term.getClass().getSimpleName();
    if (classname.endsWith("Impl")) {
      classname = classname.substring(0, classname.lastIndexOf("Impl"));
    }
    return classname;
  }

}
