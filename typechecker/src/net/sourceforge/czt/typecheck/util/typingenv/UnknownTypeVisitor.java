package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.util.Visitor;


/**
 * A visitor for UnknownType
 */
public interface UnknownTypeVisitor extends Visitor
{
  Object visitUnknownType(UnknownType unknownType);
}
