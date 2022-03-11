/*
  Copyright 2011 Calvin Kaye, Petra Malik
  This file is part of the CZT project.

  The CZT project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CZT; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.ui;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;

public class ToATermVisitor
  implements TermVisitor<Object>
{
  private StringBuffer result = new StringBuffer();

  private void write(String str)
  {
    result.append(str);
  }

  public String getResult()
  {
    return result.toString();
  }
 
  @Override
  public Object visitTerm(Term term) {
    if (term instanceof List){
      write("[");
      handleChildren(term.getChildren());
      write("]");
    }
    else {
      String str = term.getClass().getName();
      String newString = str.substring(str.lastIndexOf('.') + 1);
      if (newString.endsWith("Impl")) {
        newString = newString.substring(0 , newString.length()-4);
      }
      write(newString);
      if (term.getChildren().length != 0) {
        write("(");
        handleChildren(term.getChildren());
        write(")");
      }
    }
    if (!term.getAnns().isEmpty()) {
      write("{");
      handleChildren(term.getAnns().toArray());
      write("}");
    }
    return null;
  }

  private void handleChildren(Object[] children) {
    for (int index = 0; index < children.length; index++) {
      if (index > 0) write(", ");
      if (children[index] instanceof Term) {
        @SuppressWarnings("unused")
		Object o = ((Term) children[index]).accept(this);
      }
      else if (children[index] != null) {
        write("\"" + children[index].toString() + "\"");
      }
      else {
        write("null");
      }
    }
  }
}