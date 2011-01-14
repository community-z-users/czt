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

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.impl.ListTermImpl;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.visitor.*;

public class ToATermVisitor
  implements TermVisitor<Object>,
             NarrParaVisitor<Object>,
             NarrSectVisitor<Object>
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
 
  public Object visitTerm(Term term) {
    boolean isAList = false;
    if (term instanceof List){
      write("[");
      isAList = true;
    }
    else {
      String str = term.getClass().getName();
      String newString = str.substring(str.lastIndexOf('.') + 1);
      if (newString.contains("Impl")) {
        newString = newString.substring(0 , newString.indexOf("Impl"));
      }
      if (term.getChildren().length != 0) {
        write(newString + "(");
      }
      else {
        write(newString);
      }
    }
    int index = 0;
    for (Object obj : term.getChildren()) {
      if(obj instanceof Term){
        Term t = (Term) obj;
        Object o = t.accept(this);
        if (o != null) {
          if (index < term.getChildren().length - 1) {
            if (index != term.getChildren().length - 1
                && !(term.getChildren()[index+1] instanceof NarrPara
                     && index == term.getChildren().length - 2)) {
              write(", ");
            }
          }
        }
      }
      else {
        if (obj != null) {
          write("\"" + obj.toString() + "\"");
        }
        else {
          write("null");
        }
        if (index < term.getChildren().length - 1) {
          if (index != term.getChildren().length - 1 
              && !(term.getChildren()[index+1] instanceof NarrPara &&
                   index == term.getChildren().length - 2)) {
            write(", ");
          }
        }
      }
      index++;
    }
    if (isAList) { write("]"); }
    else {
      if(term.getChildren().length != 0){
        write(")");
      }
    }
    if (term.getAnns().size() != 0) {
      write("{");
    }
    index = 0;
    for (Object obs : term.getAnns()) {
      if (obs instanceof Term) {
        Term t = (Term) obs;
        t.accept(this);
        if (index != term.getAnns().size() - 1) {
          write(", ");
        }
      }
      index++;
    }
    if (term.getAnns().size() != 0) {
      write("}");
    }
    return term;
  }

  /** Ignore narrative paragraphs. */
  public Object visitNarrPara(NarrPara para)
  {
    return null;
  }
  
  public Object visitNarrSect(NarrSect sect)
  {
    return null;
  }
}