package net.sourceforge.czt.animation.gui.generation.plugins;

import java.util.Map;

import net.sourceforge.czt.animation.gui.generation.Plugin;

import net.sourceforge.czt.z.ast.ConstDecl;

public interface VariableExtractor extends Plugin {
  public static final String optionName="variable";
  public static final String name="Variable Extractor";

  public Map/*<DeclName, VarDecl>*/ getInputVariables(ConstDecl/*<SchExpr>*/ schema);
  public Map/*<DeclName, VarDecl>*/ getOutputVariables(ConstDecl/*<SchExpr>*/ schema);
  public Map/*<DeclName, VarDecl>*/ getStateVariables(ConstDecl/*<SchExpr>*/ schema);
};
