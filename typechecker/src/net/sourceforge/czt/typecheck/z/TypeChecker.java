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

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;
import net.sourceforge.czt.util.CztLogger;

/**
 * The top-level class in the type checker classes.
 */
public class TypeChecker
  implements TermVisitor<Object>,
             ParaVisitor<Object>,
             DeclVisitor<Object>,
             ExprVisitor<Object>,
             PredVisitor<Object>
{
  //print debuging info
  protected static boolean debug_ = false;

  //a Factory for creating Z terms
  protected Factory zFactory_;

  //the SectTypeEnv for all parent specifications
  protected SectTypeEnv sectTypeEnv_;

  //the TypeEnv for local variable scopes
  protected TypeEnv typeEnv_;

  //the TypeEnv for pending global declarations
  protected TypeEnv pending_;

  //true if and only if the previous type lookup came from the pending
  //environment
  protected boolean isPending_;

  //the UnificationEnv for recording unified generic types
  protected UnificationEnv unificationEnv_;

  //a visitor for calculating carrier set
  protected CarrierSet carrierSet_;

  //a section manager
  protected SectionInfo sectInfo_;

  //for storing the name of the current section
  protected StringBuffer sectName_ = new StringBuffer("Specification");

  //the list of errors thrown by retrieving type info
  protected List<ErrorAnn> errors_;

  //the list of errors and postcheck Terms in the current paragraph
  protected List<Object> paraErrors_;

  //allow variable use before declaration
  protected boolean useBeforeDecl_ = false;

  //used for generating unique ids in names
  protected int id_ = 0;

  //the markup to use for error reporting
  protected Markup markup_;

  //used for logging warning messages.
  protected Logger logger_ = CztLogger.getLogger(TypeChecker.class);

  //the visitors used to typechecker a spec
  protected Checker<Object> specChecker_ = null;
  protected Checker<Signature> paraChecker_ = null;
  protected Checker<List<NameTypePair>> declChecker_ = null;
  protected Checker<Type2> exprChecker_ = null;
  protected Checker<UResult> predChecker_ = null;
  protected Checker<Signature> schTextChecker_ = null;
  protected Checker<ErrorAnn> postChecker_ = null;
  protected Checker<List<Type2>> charTupleChecker_ = null;

  public TypeChecker(TypeChecker info)
  {
    this(info.zFactory_.getZFactory(), info.sectInfo_);
  }

  public TypeChecker(SectionInfo sectInfo)
  {
    this(new ZFactoryImpl(), sectInfo);
  }

  public TypeChecker(ZFactory zFactory,
                     SectionInfo sectInfo)
  {
    this(zFactory, sectInfo, false);
  }

  public TypeChecker(ZFactory zFactory,
                     SectionInfo sectInfo,
                     boolean useBeforeDecl)
  {
    zFactory_ = new Factory(zFactory);
    sectInfo_ = sectInfo;
    sectTypeEnv_ = new SectTypeEnv(zFactory);
    typeEnv_ = new TypeEnv(zFactory);
    pending_ = new TypeEnv(zFactory);
    isPending_ = false;
    unificationEnv_ = new UnificationEnv(zFactory_);
    markup_ = Markup.LATEX;
    carrierSet_ = new CarrierSet();
    errors_ = zFactory_.list();
    paraErrors_ = zFactory_.list();
    useBeforeDecl_ = useBeforeDecl;
    id_ = 0;
    specChecker_ = new SpecChecker(this);
    paraChecker_ = new ParaChecker(this);
    declChecker_ = new DeclChecker(this);
    exprChecker_ = new ExprChecker(this);
    predChecker_ = new PredChecker(this);
    schTextChecker_ = new SchTextChecker(this);
    postChecker_ = new PostChecker(this);
    charTupleChecker_ = new CharTupleChecker(this);
  }

  protected void setPreamble(String sectName, SectionInfo sectInfo)
  {
    if (sectName != null && sectInfo != null) {
      sectName_.replace(0, sectName_.length(), sectName);
      sectTypeEnv_.setSection(sectName_.toString());

      SectTypeEnv sectTypeEnv = null;
      try {
        sectTypeEnv = (SectTypeEnv) sectInfo.get(new Key(sectName_.toString(),
                                                         SectTypeEnv.class));
      }
      catch (CommandException e) {
        logger_.warning("Caught exception " + e);
      }
      if (sectTypeEnv != null) {
        sectTypeEnv_ = sectTypeEnv;
      }
    }
  }

  public Object visitTerm(Term term)
  {
    return term.accept(specChecker_);
  }

  public Signature visitPara(Para para)
  {
    return para.accept(paraChecker_);
  }

  public List<NameTypePair> visitDecl(Decl decl)
  {
    return decl.accept(declChecker_);
  }

  public Object visitExpr(Expr expr)
  {
    expr.accept(exprChecker_);
    postChecker_.postCheck();
    return null;
  }

  public Object visitPred(Pred pred)
  {
    UResult solved = (UResult) pred.accept(predChecker_);
    //if the are unsolved unifications in this predicate,
    //visit it again
    if (solved == UResult.PARTIAL) {
      pred.accept(predChecker_);
    }
    postChecker_.postCheck();
    return null;
  }

  public List<? extends ErrorAnn> errors()
  {
    return errors_;
  }
}
