/*
  Copyright (C) 2004 Tim Miller
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.typecheck.z;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.impl.*;

/**
 */
public class SpecChecker
  extends Checker
  implements SpecVisitor,
             ZSectVisitor,
             ParentVisitor,
             SectVisitor
{
  public SpecChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  public Object visitSpec(Spec spec)
  {
    List<Sect> sects = spec.getSect();
    for (Sect sect : sects) {
      sect.accept(specChecker());
    }

    //sectTypeEnv().dump();

    //if there are any errors, return false
    Boolean result = Boolean.TRUE;
    if (errors().size() > 0) {
      result = Boolean.FALSE;
    }
    return result;
  }

  /**
   * Any "left over" sections.
   */
  public Object visitSect(Sect sect)
  {
    return Boolean.TRUE;
  }

  public Object visitZSect(ZSect zSect)
  {
    debug("visiting ZSect " + zSect.getName());

    sectName(zSect.getName());

    //if this section has already been declared, raise an error
    if (sectTypeEnv().isChecked(sectName())) {
      Object [] params = {zSect.getName()};
      error(zSect, ErrorMessage.REDECLARED_SECTION, params);
    }

    //set this as the new section in SectTypeEnv
    sectTypeEnv().setSection(sectName());

    //get and visit the parent sections of the current section
    List<Parent> parents = zSect.getParent();
    List<String> names = list();
    for (Parent parent : parents) {
      parent.accept(specChecker());

      if (names.contains(parent.getWord())) {
        Object [] params = {parent.getWord(), sectName()};
        error(parent, ErrorMessage.REDECLARED_PARENT, params);
      }
      else if (parent.getWord().equals(sectName())) {
        Object [] params = {parent.getWord()};
        error(parent, ErrorMessage.SELF_PARENT, params);
      }
      else {
        names.add(parent.getWord());
      }
    }

    //get and visit the paragraphs of the current section
    List<Para> paras = zSect.getPara();
    for (Para para : paras) {
      //add the global definitions to the SectTypeEnv
      Signature signature = (Signature) para.accept(paraChecker());
      List<NameTypePair> pairs = signature.getNameTypePair();
      for (NameTypePair pair : pairs) {
        //if the name already exists globally, raise an error
        if (!sectTypeEnv().add(pair.getName(), pair.getType())) {
          Object [] params = {pair.getName()};
          error(pair.getName(), ErrorMessage.REDECLARED_GLOBAL_NAME, params);
        }
      }
    }

    //post-check any previously unresolved expressions
    List errors = list();
    for (Object next : errors()) {
      if (next instanceof Expr) {
        Expr expr = (Expr) next;
        Object message = expr.accept(postChecker());
        if (message != null) {
          errors.add(message);
        }
      }
      else {
        errors.add(next);
      }
    }
    errors().clear();
    errors().addAll(errors);

    //annotate this section with the type info from this section
    //and its parents
    addAnn(zSect, sectTypeEnv().getSectTypeEnvAnn());

    //if there are any errors, return false
    Boolean result = Boolean.TRUE;
    if (errors().size() > 0) {
      result = Boolean.FALSE;
    }
    return result;
  }

  public Object visitParent(Parent parent)
  {
    sectTypeEnv().addParent(parent.getWord());

    TermA termA = (TermA) sectInfo().getInfo(parent.getWord(), ZSect.class);
    String section = sectTypeEnv().getSection();

    if (termA != null) {
      //if there is no SectTypeEnvAnn, then we must typecheck this section
      SectTypeEnvAnn ann = (SectTypeEnvAnn) termA.getAnn(SectTypeEnvAnn.class);
      if (ann == null) {
        List errors = specChecker().typecheck(termA, sectInfo());
        errors().addAll(errors);
        ann = (SectTypeEnvAnn) termA.getAnn(SectTypeEnvAnn.class);
      }

      List<NameSectTypeTriple> triples = ann.getNameSectTypeTriple();
      for (NameSectTypeTriple triple : triples) {
        sectTypeEnv().addParent(triple.getSect());
        sectTypeEnv().add(triple);
      }
      sectTypeEnv().setSection(section);
    }
    return null;
  }
}
