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
package net.sourceforge.czt.typecheck.tcoz;

import java.util.List;

import static net.sourceforge.czt.typecheck.oz.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.tcoz.ast.*;
import net.sourceforge.czt.tcoz.util.TcozString;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.typecheck.oz.ErrorAnn;
import net.sourceforge.czt.typecheck.tcoz.util.*;
import net.sourceforge.czt.typecheck.tcoz.impl.*;

/**
 * A super class for the *Checker classes in the typechecker.
 */
abstract public class Checker<R>
  extends net.sourceforge.czt.typecheck.oz.Checker<R>
{
  //the information required for the typechecker classes.
  protected TypeChecker typeChecker_;

  public Checker(TypeChecker typeChecker)
  {
    super(typeChecker);
    typeChecker_ = typeChecker;
  }

  //a Factory for creating Object-Z terms
  protected Factory factory()
  {
    return typeChecker_.tcozFactory_;
  }

  protected void error(Term term,
		       net.sourceforge.czt.typecheck.oz.ErrorMessage error,
		       Object [] params)
  {
    ErrorAnn errorAnn = this.errorAnn(term, error, params);
    error(term, errorAnn);
  }

  protected void error(Term term,
                       net.sourceforge.czt.typecheck.z.ErrorMessage error,
                       Object [] params)
  {
    ErrorAnn errorAnn = this.errorAnn(term, error.toString(), params);
    error(term, errorAnn);
  }


  public void addImplicitOps()
  {
    Signature signature = factory().createSignature();
    ZName skip = factory().createZDeclName(TcozString.SKIP);
    addOperation(skip, signature, getSelfType());
  }

  protected Type2 instantiate(Type2 type)
  {
    Type2 result = factory().createUnknownType();
    //if this is a class type, instantiate it
    if (type instanceof ChannelType) {
      ChannelType chanType = (ChannelType) type;
      result = factory().createChannelType();
    }
    //if not a class type, use the Object-Z typechecker's instantiate method
    else {
      result = super.instantiate(type);
    }
    return result;
  }
}
