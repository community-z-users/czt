package net.sourceforge.czt.animation.gui.generation.plugins;

import java.util.List;

import net.sourceforge.czt.animation.gui.generation.Plugin;

import net.sourceforge.czt.base.ast.Term;

public interface SchemaExtractor extends Plugin {
  public List/*<ConstDecl<SchExpr>>*/ getSchemas(Term spec);
};
