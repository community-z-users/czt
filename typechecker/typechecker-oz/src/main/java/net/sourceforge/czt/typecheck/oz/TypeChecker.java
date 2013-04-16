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

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.util.TypeEnv;
import net.sourceforge.czt.typecheck.oz.util.*;
import net.sourceforge.czt.typecheck.oz.impl.*;

/**
 * The top-level class in the type checker classes.
 */
public class TypeChecker
  extends net.sourceforge.czt.typecheck.z.TypeChecker
{
  //operation expr typechecker
  protected Checker<Signature> opExprChecker_;

  //use to store information used in downcasting
  protected TypeEnv downcastEnv_;

  //the current class parargraph - null if we are not typechecking a
  //class paragraph
  protected ClassPara classPara_;

  //the list of primary state variables in the current class
  protected List<ZName> primary_;  

  public TypeChecker(Factory factory,
                     SectionManager sectInfo)
  {
    this(factory, sectInfo, false, true, false, false);
  }

  public TypeChecker(Factory factory,
                     SectionManager sectInfo,
		     boolean useBeforeDecl,
                     boolean recursiveTypes,
                     boolean sortDeclNames,
                     boolean useStrongTyping)
  {
    super(factory, sectInfo, useBeforeDecl, recursiveTypes, sortDeclNames);
    sectInfo_ = sectInfo;
    unificationEnv_ = new UnificationEnv(factory, useStrongTyping);
    carrierSet_ = new CarrierSet();
    specChecker_ = new SpecChecker(this);
    paraChecker_ = new ParaChecker(this);
    declChecker_ = new DeclChecker(this);
    exprChecker_ = new ExprChecker(this);
    predChecker_ = new PredChecker(this);
    schTextChecker_ = new SchTextChecker(this);
    postChecker_ = new PostChecker(this);
    opExprChecker_ = new OpExprChecker(this);
    downcastEnv_ = new TypeEnv(getFactory());
    classPara_ = null;
    primary_ = getFactory().list();
  }

  public Factory getFactory()
  {
    return (Factory) super.getFactory();
  }

  protected void setPreamble(String sectName, SectionManager sectInfo)
  {
    super.setPreamble(sectName, sectInfo);
  }
}
