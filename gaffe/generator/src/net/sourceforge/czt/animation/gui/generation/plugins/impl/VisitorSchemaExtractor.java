package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.util.List;
import java.util.ListIterator;

import net.sourceforge.czt.animation.gui.generation.Option;

import net.sourceforge.czt.animation.gui.generation.plugins.BadArgumentsException;
import net.sourceforge.czt.animation.gui.generation.plugins.SchemaExtractor;

import net.sourceforge.czt.base.ast.Term;

public final class VisitorSchemaExtractor implements SchemaExtractor {
  public Option[] getOptions() {return new Option[]{};};
  public String getHelp() {return "Finds the schemas in the Z specification.";};  

  private SchemaExtractionVisitor visitor=new SchemaExtractionVisitor();
  public List/*<ConstDecl<SchExpr>>*/ getSchemas(Term spec) {
    return visitor.getSchemas(spec);
  };    
};

