package net.sourceforge.czt.animation.gui.generation.plugins;

import java.io.OutputStream;

import java.util.List;

import net.sourceforge.czt.animation.gui.generation.Plugin;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.ast.ConstDecl;

public interface DOMInterfaceGenerator extends Plugin {
  public static final String optionName="interface";
  public static final String name="Interface Generator";

  public void generateInterface(Term specification, List/*<ConstDecl<SchExpr>>*/ schemas, 
				ConstDecl/*<SchExpr>*/ stateSchema, ConstDecl/*<SchExpr>*/ initSchema, 
				List/*<ConstDecl<SchExpr>>*/ operationSchemas, 
				VariableExtractor variableExtractor,
				DOMBeanChooser beanChooser, 
				OutputStream os);
};
