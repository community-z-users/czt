/*
  Copyright (C) 2004, 2005 Tim Miller
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
package net.sourceforge.czt.typecheck.oz;


import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.util.OzString;

/**
 */
public class SpecChecker
  extends Checker<List<NameSectTypeTriple>>
{
  //the name of the Object-Z toolkit
  public static final String OZ_TOOLKIT = "oz_toolkit";

  //a Z spec checker
  protected net.sourceforge.czt.typecheck.z.SpecChecker zSpecChecker_;

  public SpecChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zSpecChecker_ =
      new net.sourceforge.czt.typecheck.z.SpecChecker(typeChecker);

    //add the type for \oid
    ZName oidName = factory().createZDeclName(OzString.OID);
    PowerType oidType = factory().createOIDType();
    NameSectTypeTriple triple =
      factory().createNameSectTypeTriple(oidName, OZ_TOOLKIT, oidType);
    sectTypeEnv().add(triple);
  }

  public List<NameSectTypeTriple> visitTerm(Term term)
  {
    return term.accept(zSpecChecker_);
  }
}
