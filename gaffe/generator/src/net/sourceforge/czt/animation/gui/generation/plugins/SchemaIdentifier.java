package net.sourceforge.czt.animation.gui.generation.plugins;

import java.util.List;

import net.sourceforge.czt.animation.gui.generation.Plugin;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.ast.ConstDecl;

public interface SchemaIdentifier extends Plugin {
  public void identifySchemas(Term specification, List/*<ConstDecl<SchExpr>>*/ schemas) 
    throws IllegalStateException;
  public ConstDecl/*<SchExpr>*/ getStateSchema();
  public ConstDecl/*<SchExpr>*/ getInitSchema();
  public List/*<ConstDecl<SchExpr>>*/ getOperationSchemas();
};
