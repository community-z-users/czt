package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.util.Iterator;

import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.NumStroke;
import net.sourceforge.czt.z.ast.OutStroke;

import net.sourceforge.czt.z.visitor.NameVisitor;
import net.sourceforge.czt.z.visitor.InStrokeVisitor;
import net.sourceforge.czt.z.visitor.NextStrokeVisitor;
import net.sourceforge.czt.z.visitor.NumStrokeVisitor;
import net.sourceforge.czt.z.visitor.OutStrokeVisitor;

final class Name2String implements NameVisitor, InStrokeVisitor, NextStrokeVisitor, NumStrokeVisitor, OutStrokeVisitor {
  private Name2String(){};
  private final static Name2String instance=new Name2String();

  public static String toString(Name term) {
    return (String)instance.visitName(term);
  };
  public Object visitName(Name term) {
    String string=term.getWord();
    for(Iterator it=term.getStroke().iterator();it.hasNext();string+=it.next());
    return string;
  };
  public Object visitInStroke(InStroke term) {
    return "?";
  };
  public Object visitNextStroke(NextStroke term) {
    return "'";
  };
  public Object visitNumStroke(NumStroke term) {
    return ""+term.getNumber();
  };
  public Object visitOutStroke(OutStroke term) {
    return "!";
  };
};
