package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.impl.*;
import net.sourceforge.czt.util.CztLogger;

/**
 * A super class for the *Checker classes in the typechecker.
 */
class CheckerInfo
{
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
  protected SectionInfo manager_;

  //the factory for creating error messages
  protected ErrorFactory errorFactory_;

  //the list of errors thrown by retrieving type info
  protected List errors_;

  //used for logging warning messages.
  protected Logger logger_ = CztLogger.getLogger(CheckerInfo.class);

  //the visitors used to typechecker a spec
  protected SpecChecker specChecker_ = null;
  protected ParaChecker paraChecker_ = null;
  protected DeclChecker declChecker_ = null;
  protected ExprChecker exprChecker_ = null;
  protected PredChecker predChecker_ = null;

  //print debuging info
  protected static boolean debug_ = false;

  public CheckerInfo(CheckerInfo info)
  {
    this(info.factory_, info.sectTypeEnv_,
         info.errorFactory_, info.manager_);
  }

  public CheckerInfo(Factory factory,
                     SectTypeEnv sectTypeEnv,
                     SectionInfo manager)
  {
    this(factory, sectTypeEnv, new DefaultErrorFactory(manager), manager);
  }

  public CheckerInfo(Factory factory,
                     SectTypeEnv sectTypeEnv,
                     ErrorFactory errorFactory,
                     SectionInfo manager)
  {
    factory_ = factory;
    sectTypeEnv_ = sectTypeEnv;
    errorFactory_ = errorFactory;
    manager_ = manager;
    typeEnv_ = new TypeEnv(factory_);
    pending_ = new TypeEnv(factory_);
    unificationEnv_ = new UnificationEnv(factory_);
    errors_ = new ArrayList();
    specChecker_ = new SpecChecker(this);
    paraChecker_ = new ParaChecker(this);
    declChecker_ = new DeclChecker(this);
    exprChecker_ = new ExprChecker(this);
    predChecker_ = new PredChecker(this);
  }

  public Boolean typecheck(Term term)
  {
    return (Boolean) term.accept(specChecker_);
  }
}
