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

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 */
public class SpecChecker
  extends Checker<List<NameSectTypeTriple>>
  implements SpecVisitor<List<NameSectTypeTriple>>,
             ZSectVisitor<List<NameSectTypeTriple>>,
             ParentVisitor<List<NameSectTypeTriple>>,
             SectVisitor<List<NameSectTypeTriple>>,
             ZParaListVisitor<List<NameSectTypeTriple>>
{
  public SpecChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  @Override
  public List<NameSectTypeTriple> visitSpec(Spec spec)
  {
    //visit each section, and get the definition made in that section
    List<Sect> sects = spec.getSect();
    SectTypeEnvAnn specTypes =
      factory().createSectTypeEnvAnn(factory().<NameSectTypeTriple>list());
    List<NameSectTypeTriple> triples = specTypes.getNameSectTypeTriple();
    for (Sect sect : sects) { 
      List<NameSectTypeTriple> sectTypes = sect.accept(specChecker());
      for (NameSectTypeTriple triple : sectTypes) {
        if (!triples.contains(triple)) {
          triples.add(triple);
        }
      }
    }

    //add the annotation to the specification
    addAnn(spec, specTypes);

    //get the result and return it
    @SuppressWarnings("unused")
	Boolean result = getResult();
    return factory().list();
  }

  /**
   * Any "left over" sections.
   * @param sect
   */
  @Override
  public List<NameSectTypeTriple> visitSect(Sect sect)
  {
    return factory().list();
  }

  @Override
  public List<NameSectTypeTriple> visitZSect(ZSect zSect)
  {
    List<NameSectTypeTriple> result = checkZSect(zSect);
    return result;
  }

  @Override
  public List<NameSectTypeTriple> visitZParaList(ZParaList list)
  {
    checkParaList(list);
    return null;
  }

  @Override
  public List<NameSectTypeTriple> visitParent(Parent parent)
  {
    checkParent(parent);

    return null;
  }
}
