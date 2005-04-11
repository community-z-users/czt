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
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.z.impl.*;
import net.sourceforge.czt.util.CztLogger;

/**
 * The top-level class in the type checker classes.
 */
public class TypeChecker
  implements TermVisitor
{
  //print debuging info
  protected static boolean debug_ = false;

  //a Factory for creating Z terms
  protected Factory factory_;

  //the SectTypeEnv for all parent specifications
  protected SectTypeEnv sectTypeEnv_;

  //the TypeEnv for local variable scopes
  protected TypeEnv typeEnv_;

  //the TypeEnv for pending global declarations
  protected TypeEnv pending_;

  //the UnificationEnv for recording unified generic types
  protected UnificationEnv unificationEnv_;

  //a section manager
  protected SectionInfo sectInfo_;

  //for storing the name of the current section
  protected StringBuffer sectName_ = new StringBuffer("Specification");

  //the list of errors thrown by retrieving type info
  protected List errors_;

  //used for logging warning messages.
  protected Logger logger_ = CztLogger.getLogger(TypeChecker.class);

  //the visitors used to typechecker a spec
  protected Checker specChecker_ = null;
  protected Checker paraChecker_ = null;
  protected Checker declChecker_ = null;
  protected Checker exprChecker_ = null;
  protected Checker predChecker_ = null;
  protected Checker postChecker_ = null;

  public TypeChecker(TypeChecker info)
  {
    this(info.factory_.getZFactory(),
         info.sectInfo_);
  }

  public TypeChecker(SectionInfo sectInfo)
  {
    this(new ZFactoryImpl(), sectInfo);
  }

  public TypeChecker(ZFactory zFactory,
                     SectionInfo sectInfo)
  {
    factory_ = new Factory(zFactory);
    sectInfo_ = sectInfo;
    sectTypeEnv_ = new SectTypeEnv(zFactory);
    typeEnv_ = new TypeEnv(zFactory);
    pending_ = new TypeEnv(zFactory);
    unificationEnv_ = new UnificationEnv(zFactory);
    errors_ = new java.util.ArrayList();
    specChecker_ = new SpecChecker(this);
    paraChecker_ = new ParaChecker(this);
    declChecker_ = new DeclChecker(this);
    exprChecker_ = new ExprChecker(this);
    predChecker_ = new PredChecker(this);
    postChecker_ = new PostChecker(this);
  }

  public Object visitTerm(Term term)
  {
    return (Boolean) term.accept(specChecker_);
  }

  public List errors()
  {
    return errors_;
  }
}
