package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.util.List;
import java.util.ListIterator;

import net.sourceforge.czt.animation.gui.generation.plugins.BadArgumentsException;
import net.sourceforge.czt.animation.gui.generation.plugins.SchemaExtractor;

import net.sourceforge.czt.core.ast.Term;

public final class VisitorSchemaExtractor implements SchemaExtractor {
  private SchemaExtractionVisitor visitor=new SchemaExtractionVisitor();
  public void handleArgs(ListIterator/*<String>*/ args) throws BadArgumentsException {};
  public List/*<ConstDecl<SchExpr>>*/ getSchemas(Term spec) {
    return visitor.getSchemas(spec);
  };    
};

