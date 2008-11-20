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
    List<NameSectTypeTriple> result = checkZSect(zSect);
    return result;
  }

  public Object visitZParaList(ZParaList list)
  {
    checkParaList(list);
    return null;
  }

  public Object visitParent(Parent parent)
  {
    String parentName = parent.getWord();
    sectTypeEnv().addParent(parentName);

    //get the global decl information for the parent
    SectTypeEnvAnn sectTypeEnvAnn = null;
    try {
      sectTypeEnvAnn = sectInfo().get(new Key<SectTypeEnvAnn>(parentName, SectTypeEnvAnn.class));
    }
    catch (CommandException e) {
      final String msg = "No type information for section " + parentName;
      throw new RuntimeException(msg, e);
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
}
