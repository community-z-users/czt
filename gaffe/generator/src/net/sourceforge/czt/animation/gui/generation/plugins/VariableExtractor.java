package net.sourceforge.czt.animation.gui.generation.plugins;

import java.util.Map;

import net.sourceforge.czt.animation.gui.generation.Plugin;

import net.sourceforge.czt.core.ast.ConstDecl;

public interface VariableExtractor extends Plugin {
  public Map/*<DeclName, VarDecl>*/ getInputVariables(ConstDecl/*<SchExpr>*/ schema);
  public Map/*<DeclName, VarDecl>*/ getOutputVariables(ConstDecl/*<SchExpr>*/ schema);
};
