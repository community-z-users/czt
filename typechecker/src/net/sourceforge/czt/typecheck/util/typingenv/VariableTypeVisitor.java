package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.util.Visitor;

/**
 * A visitor for VariableType.
 */
public interface VariableTypeVisitor extends Visitor
{
  Object visitVariableType(VariableType variableType);
}
