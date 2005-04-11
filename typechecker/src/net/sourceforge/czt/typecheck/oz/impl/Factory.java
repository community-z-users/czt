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
package net.sourceforge.czt.typecheck.oz.impl;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * A factory for creating types that hide VariableTypes.
 */
public class Factory
  extends net.sourceforge.czt.typecheck.z.impl.Factory
{
  /** The OzFactory that is used to create wrapped types. */
  protected OzFactory ozFactory_;

  public Factory()
  {
    zFactory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    ozFactory_ = new net.sourceforge.czt.oz.impl.OzFactoryImpl();
  }

  public Factory(ZFactory zFactory)
  {
    zFactory_ = zFactory;
    ozFactory_ = new net.sourceforge.czt.oz.impl.OzFactoryImpl();
  }

  public Factory(ZFactory zFactory, OzFactory ozFactory)
  {
    zFactory_ = zFactory;
    ozFactory_ = ozFactory;
  }

  public OzFactory getOzFactory()
  {
    return ozFactory_;
  }

  public ClassRefType createClassRefType(ClassSig classSig,
                                         ClassRef thisClass,
                                         java.util.List superClass,
                                         VisibilityList visibilityList)
  {
    ClassRefType classRefType =
      ozFactory_.createClassRefType(classSig, thisClass,
                                    superClass, visibilityList);
    ClassRefType result = new ClassRefTypeImpl(classRefType);
    return result;
  }

  public VariableClassType createVariableClassType()
  {
    return new VariableClassType();
  }

  public VariableClassSig createVariableClassSig()
  {
    return new VariableClassSig(this);
  }

  public ClassSig createClassSig()
  {
    return ozFactory_.createClassSig();
  }

  public ClassSig createClassSig(List classes,
                                 Signature state,
                                 List attribute,
                                 List operation)
  {
    return ozFactory_.createClassSig(classes, state,
                                     attribute, operation);
  }

  public NameSignaturePair createNameSignaturePair(DeclName declName,
                                                   Signature signature)
  {
    NameSignaturePair pair =
      ozFactory_.createNameSignaturePair(declName, signature);
    NameSignaturePair result = new NameSignaturePairImpl(pair);
    return result;
  }

  public PowerType createBoolType()
  {
    Signature signature = zFactory_.createSignature();
    SchemaType schemaType = zFactory_.createSchemaType(signature);
    PowerType result = zFactory_.createPowerType(schemaType);
    return result;
  }
}
