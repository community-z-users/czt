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

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 */
public class SpecChecker
  extends Checker<Object>
  implements SpecVisitor<Object>,
             ZSectVisitor<Object>,
             ParentVisitor<Object>,
             SectVisitor<Object>
{
  public SpecChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  public Object visitSpec(Spec spec)
  {
    //visit each section, and get the definition made in that section
    List<Sect> sects = spec.getSect();
    SectTypeEnvAnn specTypes =
      factory().createSectTypeEnvAnn(GlobalDefs.<NameSectTypeTriple>list());
    List<NameSectTypeTriple> triples = specTypes.getNameSectTypeTriple();
    for (Sect sect : sects) {
      List<NameSectTypeTriple> sectTypes =
        (List<NameSectTypeTriple>) sect.accept(specChecker());
      for (NameSectTypeTriple triple : sectTypes) {
        if (!triples.contains(triple)) {
          triples.add(triple);
        }
      }
    }

    //add the annotation to the specification
    addAnn(spec, specTypes);

    //get the result and return it
    Boolean result = getResult();
    return result;
  }

  /**
   * Any "left over" sections.
   */
  public Object visitSect(Sect sect)
  {
    return list();
  }

  public Object visitZSect(ZSect zSect)
  {
    final String prevSectName = sectName();

    //set the section name
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
      Signature signature = para.accept(paraChecker());
      List<NameTypePair> pairs = signature.getNameTypePair();
      for (NameTypePair pair : pairs) {
        //if the name already exists globally, raise an error
        ZDeclName zDeclName = pair.getZDeclName();
        if (!sectTypeEnv().add(zDeclName, pair.getType())) {
          Object [] params = {zDeclName};
          error(zDeclName, ErrorMessage.REDECLARED_GLOBAL_NAME, params);
        }
      }

      //only check on the final traversal of the tree
      if (!useBeforeDecl() || sectTypeEnv().getSecondTime()) {
        postCheck();
      }
    }

    if (useBeforeDecl() && sectTypeEnv().getSecondTime()) {
      try {
        SectTypeEnv sectTypeEnv =
          (SectTypeEnv) sectInfo().get(new Key(sectName(), SectTypeEnv.class));
        assert sectTypeEnv != null;
        sectTypeEnv().overwriteTriples(sectTypeEnv.getTriple());
      }
      catch (Exception e) {
        assert false : "No SectTypeEnv for " + sectName();
      }

    }
    else {
      sectInfo().put(new Key(sectName(), SectTypeEnv.class), sectTypeEnv(), set());
    }

    if (useBeforeDecl() && !sectTypeEnv().getSecondTime()) {
      errors().clear();
      paraErrors().clear();
      removeErrorAndTypeAnns(zSect);
      sectTypeEnv().setSecondTime(true);
      zSect.accept(specChecker());
    }
    else {
      sectTypeEnv().setSecondTime(false);
    }

    //annotate this section with the type info from this section
    //and its parents
    SectTypeEnvAnn sectTypeEnvAnn = sectTypeEnv().getSectTypeEnvAnn();
    addAnn(zSect, sectTypeEnvAnn);

    sectName(prevSectName);
    sectTypeEnv().setSection(sectName());

    //get the result and return it
    Boolean typecheckResult = getResult();
    if (typecheckResult == Boolean.FALSE) {
      removeTypeAnns(zSect);
    }

    List<NameSectTypeTriple> result = sectTypeEnvAnn.getNameSectTypeTriple();
    return result;
  }

  public Object visitParent(Parent parent)
  {
    String parentName = parent.getWord();
    sectTypeEnv().addParent(parentName);

    TermA termA = null;
    try {
      termA = (TermA) sectInfo().get(new Key(parentName, ZSect.class));
    }
    catch (CommandException e) {
      assert false;
    }

    String section = sectTypeEnv().getSection();
    if (termA != null) {
      //if there is no SectTypeEnvAnn, then we must typecheck this section
      SectTypeEnvAnn ann = (SectTypeEnvAnn) termA.getAnn(SectTypeEnvAnn.class);
      if (ann == null) {
        List<? extends ErrorAnn> errors = specChecker().typecheck(termA, sectInfo());
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



  /**
   * Return the result result of the typechecking process -- FALSE if
   * there are any error messages, TRUE otherwise.
   */
  protected Boolean getResult()
  {
    Boolean result = Boolean.TRUE;
    if (errors().size() > 0) {
      result = Boolean.FALSE;
    }
    return result;
  }
}
