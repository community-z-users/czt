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
import java.util.logging.Level;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.impl.Factory;
import net.sourceforge.czt.typecheck.z.util.CarrierSet;
import net.sourceforge.czt.typecheck.z.util.DependencyGraph;
import net.sourceforge.czt.typecheck.z.util.SectTypeEnv;
import net.sourceforge.czt.typecheck.z.util.TypeEnv;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.typecheck.z.util.UnificationEnv;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.visitor.DeclVisitor;
import net.sourceforge.czt.z.visitor.ExprVisitor;
import net.sourceforge.czt.z.visitor.ParaVisitor;
import net.sourceforge.czt.z.visitor.PredVisitor;


/**
 * <p>
 * The top-level class in the type checker classes.
 * </p>
 *<p>
 * It separates the various Term categories across 
 * a series of different checker classes that can be
 * plugged in by different extensions, so that surgical
 * reuse of code can be achieved. This is important 
 * bacause Z extensions might want to change/upgrade
 * specific parts of the AST accordingly.
 *</p>
 */
public class TypeChecker
  implements TermVisitor<Object>,
             ParaVisitor<Object>,
             DeclVisitor<Object>,
             ExprVisitor<Object>,
             PredVisitor<Object>,
             TypecheckPropertiesKeys
{
  //print debuging info
  static boolean debug_ = PROP_TYPECHECK_DEBUG_DEFAULT;

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

  //the dependency graph for calculating use before declaration
  //dependencies
  protected DependencyGraph<Integer> dependencies_;

  //a visitor for calculating carrier set
  protected CarrierSet carrierSet_;

  //a section manager
  protected SectionManager sectInfo_;

  //for storing the name of the current section
  private final StringBuffer sectName_ = new StringBuffer("Specification");

  //the list of errors thrown by retrieving type info
  protected List<ErrorAnn> errors_;

  //the list of errors and postcheck Terms in the current paragraph
  protected List<Object> paraErrors_;

  //the list of undeclared names
  protected List<ZName> undeclaredNames_;

  //allow recursive types
  protected boolean useBeforeDecl_ = PROP_TYPECHECK_USE_BEFORE_DECL_DEFAULT;

  //allow recursive types
  protected boolean recursiveTypes_ = PROP_TYPECHECK_RECURSIVE_TYPES_DEFAULT;
  
  //allow decl names to be alphabetically sorted
  protected boolean sortDeclNames_ = PROP_TYPECHECK_SORT_DECL_NAMES_DEFAULT;

  //the markup to use for error reporting
  protected Markup markup_;

  //used for logging warning messages.
  protected Logger logger_ = CztLogger.getLogger(TypeChecker.class);

  //the visitors used to typechecker a spec
  protected Checker<List<NameSectTypeTriple>> specChecker_ = null;
  protected Checker<Signature> paraChecker_ = null;
  protected Checker<List<NameTypePair>> declChecker_ = null;
  protected Checker<Type2> exprChecker_ = null;
  protected Checker<UResult> predChecker_ = null;
  protected Checker<Signature> schTextChecker_ = null;
  protected Checker<ErrorAnn> postChecker_ = null;
  protected Checker<List<Type2>> charTupleChecker_ = null;

  public TypeChecker(Factory factory,
                     SectionManager sectInfo)
  {
    this(factory, 
	 sectInfo,
	 PROP_TYPECHECK_USE_BEFORE_DECL_DEFAULT,
	 PROP_TYPECHECK_RECURSIVE_TYPES_DEFAULT, 
	 PROP_TYPECHECK_SORT_DECL_NAMES_DEFAULT);
  }

  public TypeChecker(Factory factory,
                     boolean useBeforeDecl,
                     SectionManager sectInfo)
  {
    this(factory, 
	 sectInfo,
	 useBeforeDecl,
	 PROP_TYPECHECK_RECURSIVE_TYPES_DEFAULT, 
	 PROP_TYPECHECK_SORT_DECL_NAMES_DEFAULT);
  }

  public TypeChecker(Factory factory,
                     SectionManager sectInfo, 
                     boolean useBeforeDecl,
                     boolean recursiveTypes)
  {
    this(factory, 
	 sectInfo, 
	 useBeforeDecl, 
	 recursiveTypes,
	 PROP_TYPECHECK_SORT_DECL_NAMES_DEFAULT);
  }

  public TypeChecker(Factory factory,
                     SectionManager sectInfo,
                     boolean useBeforeDecl,
                     boolean recursiveTypes,
                     boolean sortDeclNames)
  {
    sectInfo_ = sectInfo;
    sectTypeEnv_ = new SectTypeEnv(factory);
    typeEnv_ = new TypeEnv(factory);
    pending_ = new TypeEnv(factory);
    isPending_ = false;
    unificationEnv_ = new UnificationEnv(factory);
    dependencies_ = new DependencyGraph<Integer>();
    markup_ = Markup.LATEX;
    carrierSet_ = new CarrierSet();
    errors_ = factory.list();
    paraErrors_ = factory.list();
    undeclaredNames_ = factory.list();
    recursiveTypes_ = recursiveTypes;
    //disable use before decl if recursive types is also turned on
    //as this subsumes use before decl, but enabling both causes problems
    useBeforeDecl_ = recursiveTypes ? false : useBeforeDecl;
    sortDeclNames_ = sortDeclNames;    
    specChecker_ = new SpecChecker(this);
    paraChecker_ = new ParaChecker(this);
    declChecker_ = new DeclChecker(this);
    exprChecker_ = new ExprChecker(this);
    predChecker_ = new PredChecker(this);
    schTextChecker_ = new SchTextChecker(this);
    postChecker_ = new PostChecker(this);
    charTupleChecker_ = new CharTupleChecker(this);
  }
  
  protected SectionManager getManager()
  {
	  return sectInfo_;
  }
  
  protected void setSectName(String sectName)
  {
    sectName_.replace(0, sectName_.length(), sectName);
  }
  
  protected String getSectName()
  {
    return sectName_.toString();
  }

  /**
   * <p>
   * This method retrieves the SectTypeEnv from the given section name
   * within the given section manager, and add all (parent) declarations 
   * to the current section being typechecked. It should be called by
   * child sections to include type information from parent sections.
   * </p>
   * <p>
   * Whilst retrieving the SectTypeEnv, the parent section is parsed
   * and typechecked implicitly through the SectionManager command for
   * SectTypeEnvAnn. If an error occurs and the parent section type
   * information cannot be retrieved, a warning is logged and no type
   * information from the parent section is added for typechecking the
   * current (child) section.
   * </p>
   */
  protected void setPreamble(String sectName, SectionManager sectInfo)
  {
    if (sectName != null && sectInfo != null) {
      setSectName(sectName);
      sectTypeEnv_.setSection(getSectName());

      SectTypeEnvAnn sectTypeEnvAnn = null;
      try {
        sectTypeEnvAnn = sectInfo.get(new Key<SectTypeEnvAnn>(getSectName().toString(),
                                                               SectTypeEnvAnn.class));
      }
      catch (CommandException e) {
        logger_.log(Level.WARNING, "Could not parse and typecheck parent section {0} because a command exception was thrown: {1}", new Object[]{getSectName().toString(), e});
      }
      if (sectTypeEnvAnn != null) {
        //add the parent's global decls to this section's global type environment
        for (NameSectTypeTriple triple : sectTypeEnvAnn.getNameSectTypeTriple()) {
          sectTypeEnv_.addParent(triple.getSect());
          sectTypeEnv_.add(triple);     
        }
      }
    }
  }

  public void setUseNameIds(boolean useNameIds)
  {
    sectTypeEnv_.setUseNameIds(useNameIds);
    typeEnv_.setUseNameIds(useNameIds);
  }

  public Factory getFactory()
  {
    return sectTypeEnv_.getFactory();
  }

  @Override
public Object visitTerm(Term term)
  {
    return term.accept(specChecker_);
  }

  @Override
public Signature visitPara(Para para)
  {
    return para.accept(paraChecker_);
  }

  @Override
public List<NameTypePair> visitDecl(Decl decl)
  {
    return decl.accept(declChecker_);
  }

  @Override
public Object visitExpr(Expr expr)
  {
    expr.accept(exprChecker_);
    postChecker_.postCheck();
    return null;
  }

  @Override
public Object visitPred(Pred pred)
  {
    UResult solved = pred.accept(predChecker_);
    //if there are unsolved unifications in this predicate,
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
