package net.sourceforge.czt.animation.gui.generation.plugins;

import net.sourceforge.czt.animation.gui.generation.Plugin;

import net.sourceforge.czt.core.ast.ConstDecl;
import net.sourceforge.czt.core.ast.DeclName;
import net.sourceforge.czt.core.ast.Term;
import net.sourceforge.czt.core.ast.VarDecl;

import org.w3c.dom.Element;

public static interface DOMBeanChooser extends Plugin {
  public Element chooseBean(Term specification, ConstDecl/*<SchExpr>*/ schema, 
			    DeclName variableName, VarDecl variableDeclaration);
};
