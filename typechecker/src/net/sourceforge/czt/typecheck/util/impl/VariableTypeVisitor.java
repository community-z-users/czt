package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.util.Visitor;

/**
 * A visitor for VariableType.
 */
public interface VariableTypeVisitor extends Visitor
{
  Object visitVariableType(VariableType variableType);
}
