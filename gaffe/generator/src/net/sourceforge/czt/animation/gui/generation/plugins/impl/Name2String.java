/*
  GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
  Copyright 2003 Nicholas Daley
  
  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.
  
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.util.Iterator;

import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.NumStroke;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.Stroke;

import net.sourceforge.czt.z.visitor.NameVisitor;
import net.sourceforge.czt.z.visitor.InStrokeVisitor;
import net.sourceforge.czt.z.visitor.NextStrokeVisitor;
import net.sourceforge.czt.z.visitor.NumStrokeVisitor;
import net.sourceforge.czt.z.visitor.OutStrokeVisitor;

/**
 * Class for turning a corejava Z Name into a Java String.
 * This class is a singleton.  Use the static method {@link #toString(Name) toString(Name)}.
 * @author Nicholas Daley
 */
final class Name2String implements NameVisitor, InStrokeVisitor, NextStrokeVisitor, NumStrokeVisitor, OutStrokeVisitor {
  /**
   * Constructor private, because this is a Singleton.
   */
  private Name2String(){};
  /**
   * The class's single instance.
   */
  private final static Name2String instance=new Name2String();

  /**
   * Translates a name into a String, uses <tt>instance</tt> as a visitor on the name.
   * @param name The name to translate.
   */
  public static String toString(Name name) {
    return (String)instance.visitName(name);
  };
  /**
   * Visitor method which translates a name.
   */
  public Object visitName(Name term) {
    String string=term.getWord();
    for(Iterator it=term.getStroke().iterator();it.hasNext();)
      string+=((Stroke)it.next()).accept(this);
    return string;
  };
  /**
   * Visitor method which translates <tt>InStroke</tt>s.
   */
  public Object visitInStroke(InStroke term) {
    return "?";
  };
  /**
   * Visitor method which translates <tt>NextStroke</tt>s.
   */
  public Object visitNextStroke(NextStroke term) {
    return "'";
  };
  /**
   * Visitor method which translates <tt>NumStroke</tt>s.
   */
  public Object visitNumStroke(NumStroke term) {
    return ""+term.getNumber();
  };
  /**
   * Visitor method which translates <tt>OutStroke</tt>s.
   */
  public Object visitOutStroke(OutStroke term) {
    return "!";
  };
};
