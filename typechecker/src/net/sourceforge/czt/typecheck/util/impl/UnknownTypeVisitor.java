package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.util.Visitor;


/**
 * A visitor for UnknownType.
 */
public interface UnknownTypeVisitor extends Visitor
{
  Object visitUnknownType(UnknownType unknownType);
}
