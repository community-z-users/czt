package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.ArrayList;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.impl.*;
import net.sourceforge.czt.util.CztLogger;

/**
 * A super class for the *Checker classes in the typechecker.
 */
class CheckerInfo
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

  //the factory for creating error messages
  protected ErrorFactory errorFactory_;

  //for storing the name of the current section
  protected StringBuffer sectName_ = new StringBuffer("Specification");

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
  protected PostChecker postChecker_ = null;

  public CheckerInfo(CheckerInfo info)
  {
    this(info.factory_.getZFactory(), info.sectTypeEnv_,
         info.errorFactory_, info.sectInfo_);
  }

  public CheckerInfo(ZFactory zFactory,
                     SectTypeEnv sectTypeEnv,
                     SectionInfo sectInfo)
  {
    this(zFactory, sectTypeEnv, new DefaultErrorFactory(sectInfo), sectInfo);
  }

  public CheckerInfo(ZFactory zFactory,
                     SectTypeEnv sectTypeEnv,
                     ErrorFactory errorFactory,
                     SectionInfo sectInfo)
  {
    factory_ = new Factory(zFactory);
    sectTypeEnv_ = sectTypeEnv;
    errorFactory_ = errorFactory;
    sectInfo_ = sectInfo;
    typeEnv_ = new TypeEnv(zFactory);
    pending_ = new TypeEnv(zFactory);
    unificationEnv_ = new UnificationEnv(zFactory);
    errors_ = new ArrayList();
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
