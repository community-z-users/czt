package net.sourceforge.czt.animation.gui.generation.plugins;

import net.sourceforge.czt.animation.gui.generation.Plugin;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.VarDecl;

import org.w3c.dom.Element;

public interface DOMBeanChooser extends Plugin {
  /**
   * @param specification Term containing the Spec, Sect, or Para the schema was found in.
   * @param schema The schema that contains the variable.
   * @param variableName The name of the variable the bean is for.
   * @param variableDeclaration The VarDecl in which the variable was declared.
   * @param availableSpace The amount of space available for the bean, or null if there is no limit.
   * @param sizeOut The actual size of the bean is recorded here by chooseBean.
   * @return The Element containing the XML to write to the file 
   */
  public Element chooseBean(Term specification, ConstDecl/*<SchExpr>*/ schema, 
			    DeclName variableName, VarDecl variableDeclaration);
};
