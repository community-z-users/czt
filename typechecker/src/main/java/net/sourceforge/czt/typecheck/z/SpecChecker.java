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
             SectVisitor<Object>,
             ZParaListVisitor<Object>
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
      factory().createSectTypeEnvAnn(factory().<NameSectTypeTriple>list());
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
    return factory().list();
  }

  public Object visitZSect(ZSect zSect)
  {
    final String prevSectName = sectName();

    //set the section name
    setSectName(zSect.getName());

    //set the markup for this section
    setMarkup(zSect);

    //if this section has already been declared, raise an error
    if (sectTypeEnv().isChecked(sectName()) &&
        !sectTypeEnv().getUseNameIds()) {
      Object [] params = {zSect.getName()};
      error(zSect, ErrorMessage.REDECLARED_SECTION, params);
    }

    //set this as the new section in SectTypeEnv
    sectTypeEnv().setSection(sectName());

    //get and visit the parent sections of the current section
    List<Parent> parents = zSect.getParent();
    List<String> names = factory().list();
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
    zSect.getParaList().accept(this);

    if ((useBeforeDecl() && sectTypeEnv().getSecondTime()) ||
        sectTypeEnv().getUseNameIds()) {
      try {
        SectTypeEnvAnn sectTypeEnvAnn =
          (SectTypeEnvAnn) sectInfo().get(new Key(sectName(), SectTypeEnvAnn.class));
        assert sectTypeEnvAnn != null;
        sectTypeEnv().overwriteTriples(sectTypeEnvAnn.getNameSectTypeTriple());
      }
      catch (CommandException e) {
        assert false : "No SectTypeEnvAnn for " + sectName();
      }
    }
    else {
      SectTypeEnvAnn sectTypeEnvAnn = sectTypeEnv().getSectTypeEnvAnn();
      sectInfo().put(new Key(sectName(), SectTypeEnvAnn.class),
                     sectTypeEnvAnn, new java.util.HashSet());
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

    setSectName(prevSectName);
    sectTypeEnv().setSection(sectName());

    //get the result and return it
    Boolean typecheckResult = getResult();
    if (typecheckResult == Boolean.FALSE) {
      removeTypeAnns(zSect);
    }

    //create the SectTypeEnvAnn and add it to the section information
    List<NameSectTypeTriple> result = sectTypeEnvAnn.getNameSectTypeTriple();
    return result;
  }

  public Object visitZParaList(ZParaList list)
  {
    for (Para para : list) {
      //add the global definitions to the SectTypeEnv
      Signature signature = para.accept(paraChecker());
      List<NameTypePair> pairs = signature.getNameTypePair();
      for (NameTypePair pair : pairs) {
        //if the name already exists globally, raise an error
        ZName zName = pair.getZName();
        NameSectTypeTriple duplicate =
          sectTypeEnv().add(zName, pair.getType());
        if (duplicate != null) {
          Object [] params = {zName};
          error(zName, ErrorMessage.REDECLARED_GLOBAL_NAME, params);
        }
      }

      //only check on the final traversal of the tree
      if (!useBeforeDecl() || sectTypeEnv().getSecondTime()) {
        postCheck();
      }
    }
    return null;
  }

  public Object visitParent(Parent parent)
  {
    String parentName = parent.getWord();
    sectTypeEnv().addParent(parentName);

    //get the global decl information for the parent
    SectTypeEnvAnn sectTypeEnvAnn = null;
    try {
      sectTypeEnvAnn =
        (SectTypeEnvAnn) sectInfo().get(new Key(parentName,
                                                SectTypeEnvAnn.class));
    }
    catch (CommandException e) {
      assert false : "No type information for section " + parentName;
      e.printStackTrace();
    }

    //add the parent's global decls to this section's global type environment
    for (NameSectTypeTriple triple : sectTypeEnvAnn.getNameSectTypeTriple()) {
      sectTypeEnv().addParent(triple.getSect());
      NameSectTypeTriple duplicate = sectTypeEnv().add(triple);
      //raise an error if there are duplicates in merging parents
      if (duplicate != null &&
          !duplicate.getSect().equals(triple.getSect())) {
        Object [] params = {triple.getZName(), duplicate.getSect(),
                            triple.getSect(), sectName()};
        error(parent, ErrorMessage.REDECLARED_GLOBAL_NAME_PARENT_MERGE, params);
      }
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
