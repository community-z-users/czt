package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;

import net.sourceforge.czt.animation.gui.generation.plugins.BadArgumentsException;
import net.sourceforge.czt.animation.gui.generation.plugins.VariableExtractor;

import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.VarDecl;

public final class DefaultVariableExtractor implements VariableExtractor {
  private Map/*<DeclName, VarDecl>*/ getXVariables(ConstDecl/*<SchExpr>*/ schema, Class clazz) {
    Map results/*<DeclName, VarDecl>*/=new HashMap/*<DeclName, VarDecl>*/();
    List declarations=((SchExpr)schema.getExpr()).getSchText().getDecl();
    for(Iterator it=declarations.iterator();it.hasNext();) {
      VarDecl declaration;
      try {
	declaration=(VarDecl)it.next();
      } catch(ClassCastException ex) {
	continue;
      }
      for(Iterator itn=declaration.getDeclName().iterator();itn.hasNext();) {
	DeclName name=(DeclName)itn.next();
	if(name.getStroke().size()==0) continue;
	Stroke lastStroke=(Stroke)name.getStroke().get(name.getStroke().size()-1);
	if(clazz.isInstance(lastStroke)) results.put(name,declaration);
      }
    }
    return results;
  };
  public Map/*<DeclName, VarDecl>*/ getInputVariables(ConstDecl/*<SchExpr>*/ schema) {
    return getXVariables(schema,InStroke.class);
  };
  public Map/*<DeclName, VarDecl>*/ getOutputVariables(ConstDecl/*<SchExpr>*/ schema) {
    return getXVariables(schema,OutStroke.class);
  };
  public Map/*<DeclName, VarDecl>*/ getStateVariables(ConstDecl/*<SchExpr>*/ schema) {
    return getXVariables(schema,NextStroke.class);
  };

  public void handleArgs(ListIterator args) throws BadArgumentsException {return;};
  public String getArgsDocumentation() {return "";};
};
