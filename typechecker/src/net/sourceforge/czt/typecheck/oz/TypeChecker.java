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
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.oz.impl.OzFactoryImpl;
import net.sourceforge.czt.typecheck.oz.util.*;
import net.sourceforge.czt.typecheck.oz.impl.*;

/**
 * The top-level class in the type checker classes.
 */
public class TypeChecker
  extends net.sourceforge.czt.typecheck.z.TypeChecker
{
  //a factory for object types
  protected Factory ozFactory_;

  //operation expr typechecker
  protected Checker opExprChecker_;

  //the name of the current class being typechecked - null if we are
  //not typechecking a class paragraph
  protected DeclName className_;

  //the list of primary state variables in the current class
  protected List<DeclName> primary_;

  public TypeChecker(TypeChecker info)
  {
    this(info.zFactory_.getZFactory(),
         info.ozFactory_.getOzFactory(),
         info.sectInfo_,
	 info.markup_);
  }

  public TypeChecker(SectionInfo sectInfo)
  {
    this(new ZFactoryImpl(),
         new OzFactoryImpl(),
         sectInfo,
	 Markup.UNICODE);
  }

  public TypeChecker(SectionInfo sectInfo, Markup markup)
  {
    this(new ZFactoryImpl(),
         new OzFactoryImpl(),
         sectInfo,
	 markup);
  }

  public TypeChecker(ZFactory zFactory,
                     OzFactory ozFactory,
                     SectionInfo sectInfo,
		     Markup markup)
  {
    super(sectInfo, markup);
    ozFactory_ = new Factory(zFactory, ozFactory);
    sectInfo_ = sectInfo;
    unificationEnv_ = new UnificationEnv(zFactory);
    carrierSet_ = new CarrierSet();
    specChecker_ = new SpecChecker(this);
    paraChecker_ = new ParaChecker(this);
    declChecker_ = new DeclChecker(this);
    exprChecker_ = new ExprChecker(this);
    predChecker_ = new PredChecker(this);
    postChecker_ = new PostChecker(this);
    opExprChecker_ = new OpExprChecker(this);
    className_ = null;
    primary_ = new java.util.ArrayList();
  }
}
