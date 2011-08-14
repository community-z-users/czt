/**
Copyright 2007, Leo Freitas
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.dc.z;

import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.logging.Logger;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.parser.util.ThmTable;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ParaVisitor;
import net.sourceforge.czt.z.visitor.ParentVisitor;
import net.sourceforge.czt.z.visitor.SectVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

/**
 * <p>
 * Top-level domain checking class. Given a Z section or specification, it 
 * calculates the list of conjectures for each relevant paragraph. The results
 * are delivered either as child Z section with a list of conjectures or as a
 * list of paragraph / predicate pairs. For details on the nature of domain 
 * checks and their shape for every Z term, see {@link #DCTerm}.
 * </p>
 * <p>
 * To use it properly, first one need to set the section manager where the domain
 * checker will work. Next, one can request for either a packed child DC Z sect,
 * or a list of para/pred pairs for a given Z sect or Spec. If not section manager
 * is given, parent sections won't be checked and known standard definitions won't
 * be loaded. In this case, the \appliesTo function from dc\_toolkit.tex will always
 * be used to resolve domain checking conflicts. Although this is not a problem per se,
 * it leads to more complex domain check conjectures to prove. The DC toolkit is loaded
 * once every time the section manager changes.
 * </p>
 * <p>
 * During preprocessing, which happens once per each Z section, the section's 
 * definition and operator tables (and all of its parents) are loaded. This is
 * useful so that spurious domain checking conditions (e.g., those of declared 
 * total functions or operator templates) are avoided. Finally, two fine grained
 * parameters allow one to have \appliesTo applications as infix or no fix, and
 * one can also avoid processing specific parent sections (e.g., standard toolkit).
 * </p>
 * 
 * @author leo
 */
public class DomainChecker extends AbstractDCTerm<List<Pair<Para, Pred>>>
        implements
        SectVisitor<List<Pair<Para, Pred>>>,
        ZSectVisitor<List<Pair<Para, Pred>>>,
        ParentVisitor<List<Pair<Para, Pred>>>,
        ParaVisitor<List<Pair<Para, Pred>>>,
        DomainCheckPropertyKeys
{

  private static final Logger logger_ = Logger.getLogger(DomainChecker.class.getName());
  /**
   * Various class fields
   */
  private SectionManager sectManager_;
  private ZSect dcToolkit_;
  private OpTable opTable_;
  private DefinitionTable defTable_;
  private DCTerm domainCheck_;
  private SortedSet<String> parentsToIgnore_;
  private boolean addTrivialDC_;
  private boolean processParents_;
  private boolean infixAppliesTo_;
  private boolean applyPredTransf_;
  private boolean logTypeWarnings_;
  
  /**
   * 
   */
  protected static final String[] EXTENDED_TOOLKIT_NAMES =
  {
    "whitespace",
    "fuzz_toolkit"
  };
  /**
   * 
   */
  protected static final String[] STANDARD_TOOLKIT_NAMES =
  {
    "prelude",
    "number_toolkit",
    "set_toolkit",
    "relation_toolkit",
    "function_toolkit",
    "sequence_toolkit",
    "standard_toolkit"
  };

  /* CLASS SETUP METHOS */

  public DomainChecker()
  {
    this(new Factory());
  }

  public DomainChecker(Factory factory)
  {
    super(factory);
    assert factory != null;
    domainCheck_ = new DCTerm(factory);
    parentsToIgnore_ = new TreeSet<String>();
    parentsToIgnore_.addAll(defaultParentsToIgnore());
    infixAppliesTo_ = PROP_DOMAINCHECK_USE_INFIX_APPLIESTO_DEFAULT;
    applyPredTransf_ = PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS_DEFAULT;
    addTrivialDC_ = PROP_DOMAINCHECK_ADD_TRIVIAL_DC_DEFAULT;
    logTypeWarnings_ = PROP_DOMAINCHECK_RAISE_TYPE_WARNINGS_DEFAULT;
    processParents_ = PROP_DOMAINCHECK_PROCESS_PARENTS_DEFAULT;
  }
  
  /* PROPERTY RELATED METHODS */
  /**
   * 
   */
  protected void reset()
  {
    opTable_ = null;
    defTable_ = null;
    dcToolkit_ = null;
    sectManager_ = null;
    clearParentsToIgnore();
    parentsToIgnore_.addAll(defaultParentsToIgnore());
    infixAppliesTo_ = PROP_DOMAINCHECK_USE_INFIX_APPLIESTO_DEFAULT;
    applyPredTransf_ = PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS_DEFAULT;
    addTrivialDC_ = PROP_DOMAINCHECK_ADD_TRIVIAL_DC_DEFAULT;
    logTypeWarnings_ = PROP_DOMAINCHECK_RAISE_TYPE_WARNINGS_DEFAULT;
    processParents_ = PROP_DOMAINCHECK_PROCESS_PARENTS_DEFAULT;
  }

  /**
   * Sets up available options according to the section manager's configuration.
   * It does nothing if no section manager is available.
   * @throws DomainCheckException
   */
  protected void config() throws DomainCheckException
  {
    checkSectionManager("DC-NO-SM = use default options");
    boolean useInfixAppliesTo =
      (sectManager_.hasProperty(PROP_DOMAINCHECK_USE_INFIX_APPLIESTO) ?
        sectManager_.getBooleanProperty(PROP_DOMAINCHECK_USE_INFIX_APPLIESTO) :
        PROP_DOMAINCHECK_USE_INFIX_APPLIESTO_DEFAULT);
    boolean processParents =
      (sectManager_.hasProperty(PROP_DOMAINCHECK_PROCESS_PARENTS) ?
        sectManager_.getBooleanProperty(PROP_DOMAINCHECK_PROCESS_PARENTS) :
        PROP_DOMAINCHECK_PROCESS_PARENTS_DEFAULT);
    boolean addTrivialDC =
      (sectManager_.hasProperty(PROP_DOMAINCHECK_ADD_TRIVIAL_DC) ?
        sectManager_.getBooleanProperty(PROP_DOMAINCHECK_ADD_TRIVIAL_DC) :
        PROP_DOMAINCHECK_ADD_TRIVIAL_DC_DEFAULT);
    boolean applyPredTransf =
      (sectManager_.hasProperty(PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS) ?
        sectManager_.getBooleanProperty(PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS) :
        PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS_DEFAULT);
    boolean raiseTW =
      (sectManager_.hasProperty(PROP_DOMAINCHECK_RAISE_TYPE_WARNINGS) ?
        sectManager_.getBooleanProperty(PROP_DOMAINCHECK_RAISE_TYPE_WARNINGS) :
        PROP_DOMAINCHECK_RAISE_TYPE_WARNINGS_DEFAULT);
    List<String> parentsToIgnore =
      (sectManager_.hasProperty(PROP_DOMAINCHECK_PARENTS_TO_IGNORE) ?
       sectManager_.getListProperty(PROP_DOMAINCHECK_PARENTS_TO_IGNORE) : new java.util.ArrayList<String>());

    setInfixAppliesTo(useInfixAppliesTo);
    setProcessingParents(processParents);
    setAddingTrivialDC(addTrivialDC);
    setApplyPredTransformers(applyPredTransf);
    setAddingTrivialDC(addTrivialDC);
    setRaiseTypeWarnings(raiseTW);
    clearParentsToIgnore();
    parentsToIgnore_.addAll(parentsToIgnore);
    logger_.config("DC-SM = load SM options");
  }

  /**
   * By default ignore all STANDARD_TOOLKIT_NAMES and EXTENDED_TOOLKIT_NAMES Z sections.
   * @return 
   */
  protected static SortedSet<String> defaultParentsToIgnore()
  {
    SortedSet<String> result = new TreeSet<String>(Arrays.asList(STANDARD_TOOLKIT_NAMES));
    result.addAll(Arrays.asList(EXTENDED_TOOLKIT_NAMES));
    result.add(DOMAIN_CHECK_TOOLKIT_NAME);
    return result;
  }

  /* CONFIGURATION METHODS */
  
  /**
   * Reset parameters, sets the section manager, then retrieves configuration for
   * known properties (i.e., it calls reset and config methods).
   * @param manager non-null manager
   * @throws DomainCheckException
   */
  public void setSectInfo(SectionManager manager) throws DomainCheckException
  {
    if (manager == null) 
    {
      throw new DomainCheckException("DC-SM-NULL");
    }
    // only reset if needed
    else if(sectManager_ != manager)
    {
      reset();
      sectManager_ = manager;
      config();
    }
  }

  public SectionManager getManager()
  {
    if (sectManager_ == null) { logger_.warning("DC-SM-REQUEST = null!"); }
    return sectManager_;
  }

  /**
   * Clears both sets of parents to process and to ignore
   */
  public void clearParentsToIgnore()
  {
    parentsToIgnore_.clear();
  }

  /**
   * Returns a unmodifiable set of section names not being domain checked. 
   * @return 
   */
  public SortedSet<String> getParentsToIgnore()
  {
    return Collections.unmodifiableSortedSet(parentsToIgnore_);
  }

  /**
   * 
   * @param parent
   */
  public void addParentSectionToIgnore(Parent parent)
  {
    assert parent != null;
    addParentSectionToIgnore(parent.getWord());
  }

  /**
   * 
   * @param parent
   */
  public void addParentSectionToIgnore(String parent)
  {
    assert parent != null && !parent.isEmpty() : "Invalid (null or empty) section name.";
    parentsToIgnore_.add(parent);
  }

  /**
   * 
   * @return
   */
  public boolean isUsingInfixAppliesTo()
  {
    return infixAppliesTo_;
  }

  /**
   * 
   * @param value
   */
  public void setInfixAppliesTo(boolean value)
  {
    infixAppliesTo_ = value;
  }

  /**
   * 
   * @return
   */
  public boolean isProcessingParents()
  {
    return processParents_;
  }

  public boolean isApplyingPredTransformers()
  {
    return applyPredTransf_;
  }

  public void setProcessingParents(boolean value)
  {
    processParents_ = value;
  }

  public boolean isAddingTrivialDC()
  {
    return addTrivialDC_;
  }

  public void setAddingTrivialDC(boolean value)
  {
    addTrivialDC_ = value;
  }

  public void setApplyPredTransformers(boolean value)
  {
    applyPredTransf_ = value;
  }

  public boolean isRaisingTypeWarnings()
  {
    return logTypeWarnings_;
  }

  public void setRaiseTypeWarnings(boolean value)
  {
    logTypeWarnings_ = value;
  }

  /* DC CALCULATION METHODS */

  /**
   * Loads the Domain check toolkit containing necessary definitions for the DC VCs.
   * 
   * @throws DomainCheckException
   */
  private void loadDCToolkit() throws DomainCheckException
  {
    assert sectManager_ != null : "Cannot load " + DOMAIN_CHECK_TOOLKIT_NAME + " without a section info!";
    if (dcToolkit_ == null)
    {
      // parse and typecheck the dcToolkit within the section manager so that that operator
      // table for (_appliesTo_) is available within it.
      SectTypeEnvAnn type = null;
      try
      {
        dcToolkit_ = sectManager_.get(new Key<ZSect>(DOMAIN_CHECK_TOOLKIT_NAME, ZSect.class));
        type = sectManager_.get(new Key<SectTypeEnvAnn>(DOMAIN_CHECK_TOOLKIT_NAME, SectTypeEnvAnn.class));
      }
      catch (CommandException e)
      {
        if (dcToolkit_ == null)
          throw new DomainCheckException("SEVERE: parsing error in domain check toolkit (see cause details)!", e);
        else if (type == null)
          throw new DomainCheckException("SEVERE: typing error in domain check toolkit (see cause details)!", e);
        else
          throw new DomainCheckException("SEVERE: command exception when processing DC toolkit (see cause details!)", e);
      }
      assert type != null : "Could not typecheck DC toolkit";
    }
    assert dcToolkit_ != null : "Could not load DC toolkit";
  }

  /**
   * Creates the domain check predicate list for each paragraph within the given
   * ZSect. If processParents is true, all the parents outside {@link #getParentsToIgnore()}
   * are also processed and added to the result.
   * @param zSect ZSect to calculate DC VCs for
   * @param term Z section to domain check
   * @return list of domain check predicates for each paragraph of given Z section
   * @throws DomainCheckException 
   */
  private List<Pair<Para, Pred>> processZSect(ZSect zSect)
          throws DomainCheckException
  {
    // load the toolkit, if not there already.
    loadDCToolkit();

    // if we should not process parents, just add ZSect parents to the ignore list
    if (!isProcessingParents())
    {
      for (Parent parent : zSect.getParent())
      {
        addParentSectionToIgnore(parent);
      }
    }

    List<Pair<Para,Pred>> result = null;
    try
    {
      // process ZSect for VCs
      result = collect(zSect);
      return result;
    }
    catch (CztException e)
    {
      Throwable cause = e.getCause();
      if (cause instanceof DomainCheckException)
      {
        throw (DomainCheckException)cause;
      }
      else
        throw new DomainCheckException("DC-PROCESS-ZSECT = term visit error (see details).", e);
    }
  }

//  /**
//   * Collects the list of predicates associated with the top-level paragraphs for
//   * each section within the given Spec term. The list of parents to process determines
//   * which parents should be included while processing the Spec.
//   * @param term specification to domain check
//   * @return map from section names to a list of domain check predicates for each paragraph of each Z section
//   * @throws DomainCheckException
//   */
//  protected SortedMap<String, List<Pair<Para, Pred>>> dc(Spec term)
//          throws DomainCheckException
//  {
//    assert term != null : "Invalid (null) specification!";
//
//    // process each one of the ZSect within Spec
//    SortedMap<String, List<Pair<Para, Pred>>> result = new TreeMap<String, List<Pair<Para, Pred>>>();
//    for (Sect sect : term.getSect())
//    {
//      if (sect instanceof ZSect)
//      {
//        ZSect zsect = (ZSect) sect;
//        List<Pair<Para, Pred>> dcList = processZSect(zsect);
//        List<Pair<Para, Pred>> old = result.put(zsect.getName(), dcList);
//        assert old == null : "Duplicated ZSect DC processing for " + zsect.getName();
//      }
//    }
//    return result;
//  }

  /**
   * Collects the list of domain check predicates for each paragraph within the
   * given ZSect term. If process parents is true, section parents are processed
   * and added. 
   * @param term Z section to domain check
   * @return list of domain check predicates for each paragraph of given Z section
   * @throws DomainCheckException
   */
  protected List<Pair<Para, Pred>> dc(ZSect term)
          throws DomainCheckException
  {
    assert term != null : "Invalid (null) specification!";
    List<Pair<Para, Pred>> result = processZSect(term);
    return result;
  }

  /* TERM DC COLLECTION VISITING METHODS */

  /**
   * Collect all DC predicates from the terms within the given list.
   * This could be a ZParaList, a ListTerm<Parent>, or ListTerm<Sect>,
   * which comes from ZSect.getZParaList(), ZSect.getParent(), and
   * Spec.getSect().
   * @param <T>
   * @param list
   * @return 
   */
  protected <T extends Term> List<Pair<Para, Pred>> collect(T... list)
  {
    List<Pair<Para, Pred>> result = factory_.list();
    for (T term : list)
    {
      result.addAll(term.accept(this));
    }
    return result;
  }

  protected void raiseDCExceptionWhilstVisiting(final String msg)
  {
    logger_.warning(msg);
    throw new CztException(new DomainCheckException(msg));
  }

  /**
   * Checks whether there is a section manager or not, and raises the DC error
   * wrapped up as a CztException.
   * @param info some data, usually ZSect Name, say
   * @throws DomainCheckException  if there is no section manager
   */
  protected void checkSectionManager(String info) throws DomainCheckException
  {
    if (sectManager_ == null)
    {
      final String msg = "DC-PROCESS-ERROR = No SectMngr! Couldn't retrieve DefTbl for " + info;
      logger_.severe(msg);
      throw new DomainCheckException(msg);
    }
  }

  /** TOP-LEVEL SPECIFICATION TERM PROCESSING VISITOR METHODS */

  /**
   * For UnparsedZSect or NarrSect, just return an empty list.
   * @param term
   * @return
   */
  @Override
  public List<Pair<Para, Pred>> visitSect(Sect term)
  {
    // just ignore other types of Sect
    return factory_.list();
  }

  /**
   * For parent sections, calculate their dependant domain checks,
   * or lookup in the section manager
   * @param term
   * @return
   */
  @Override
  public List<Pair<Para, Pred>> visitParent(Parent term)
  {
    String sectName = term.getWord();

    // if this is one known parent to ignore, raise an error
    if (parentsToIgnore_.contains(sectName))
    {
      final String msg = "DC-IGNORE-PARENT = " + sectName;
      logger_.info(msg);
    }
    // otherwise collect information
    else
    {
      //checkSectionManager(sectName);
      try
      {
        // calculate the domain checks for the given section. this updates the
        // section manager to contain the appropriate parent information.
        ZSectDCEnvAnn zsDCEnvAnn = sectManager_.get(new Key<ZSectDCEnvAnn>(sectName, ZSectDCEnvAnn.class));
        assert zsDCEnvAnn != null;
      }
      catch (CommandException ex)
      {
         raiseDCExceptionWhilstVisiting("DC-PROCESS-ERROR = CmdExpt: coulnd't process parents for " +
                sectName + "\n\t " + ex.getMessage());
      }
    }
    // result is always empty. the update happens at the section manager.
    return factory_.list();
  }

  @Override
  @SuppressWarnings("unchecked")
  public List<Pair<Para, Pred>> visitZSect(ZSect term)
  {
    String sectName = term.getName();
    //checkSectionManager(sectName);

    // attempt retrieving defintion + operator tables.
    try
    {
      // retrieve definition + operator tables for Z section being analysed
      defTable_ = sectManager_.get(new Key<DefinitionTable>(sectName, DefinitionTable.class));
    }
    catch (CommandException e)
    {
      defTable_ = null;
      if (e instanceof DefinitionTable.DefinitionException)
      {
        logger_.warning("VCG-DEFTBL-ZSECT-ERROR = " + sectName +
                "\n\t " + e.getMessage());
      }
      else
      {
        raiseDCExceptionWhilstVisiting("VCG-VISIT-ZSECT-ERROR = CmdExpt @ DefTable for: " + sectName
              /*+ "(i.e., can only use AppliesTo rather than \\dom)."*/ + "\n\t " + e.getMessage());
      }
    }
    try
    {
      opTable_ = sectManager_.get(new Key<OpTable>(sectName, OpTable.class));
    }
    catch (CommandException e)
    {
      opTable_ = null;
      raiseDCExceptionWhilstVisiting("DC-PROCESS-ERROR = CmdExpt: coulnd't retrieve OpTable for " + sectName +
                "\n\t " + e.getMessage());
    }

    List<Pair<Para, Pred>> result = factory_.list();

    // process section parents
    result.addAll(collect(term.getParent().toArray(new Parent[0])));

    // collect all DC predicates from the declared paragraphs
    result.addAll(collect(term.getZParaList().toArray(new Para[0])));

    // clear definition and operator tables
    defTable_ = null;
    opTable_ = null;

    // return collected predicates
    return result;
  }

  /**
   * Retrieves for the given paragraph a corresponding domain check predicate
   * based over information on the current definition table.
   * 
   * @param term
   * @return
   */
  @Override
  public List<Pair<Para, Pred>> visitPara(Para term)
  {
    List<Pair<Para, Pred>> result = factory_.list();

    // collect DC predicates for the given ZSect paragraph with 
    // infered defTable and chosen infix form for \appliesTo.
    //
    // defTable_ is initialised at visitZSect ; null otherwise, in which 
    // case \appliesTo is always used since we cannot know about \dom info.
    Pred dcPred = domainCheck_.runDC(term, defTable_, isUsingInfixAppliesTo(), isApplyingPredTransformers());
    Pair<Para, Pred> pair = new Pair<Para, Pred>(term, dcPred);
    result.add(pair);
    return result;
  }

  /* AUXILIARY TERM PROCESSING METHODS */

  /**
   * Logs type ErrorAnn as warning if ERROR or if raising type checking warnings.
   * The result is the same as <code>errors.size()</code>, if <code>isRaisingTypeWarnings()</code>;
   * it is the same as the number of ERROR elements (e.g., don't raise warnings) otherwise.
   *
   * To be called only by typeCheck method below.
   *
   * @param errors list of type errors
   * @return number of errors (and maybe warnings) print.
   */
  protected int printErrors(List<? extends ErrorAnn> errors)
  {
    int result = 0;
    //print any errors
    for (ErrorAnn next : errors)
    {
      // raiseWarnings => next.getErrorType(ErrorType.ERROR) only
      if (logTypeWarnings_ || next.getErrorType().equals(ErrorType.ERROR))
      {
        // TODO: fix this? It might generate section management problems in case of
        //       systemic management error / failure :-( = toString uses the SectionManager
        logger_.warning(next.toString());
        result++;
      }
    }
    return result;
  }

  /**
   * Like in Parser.xml, we need to add OpTable and ThmTable (and other tables)
   * for ZSections created on-the-fly (e.g., DC ZSect).
   *
   * To be called only by methods creating ZSects on the fly.
   *
   * @param zSect DC ZSect (or on the fly ones)
   * @throws DomainCheckException
   */
  private void updateManager(ZSect zSect)
          throws DomainCheckException
  {
    assert sectManager_ != null;
    try
    {
      ParseUtils.updateSectManager(sectManager_, zSect);
    }
    catch (CommandException e)
    {
      final String msg = "DC-CMDEXP-TBL = " + e.getCause();
      logger_.warning(msg);
      throw new DomainCheckException(msg, e);
    }
  }

  /**
   * Type checks the given section name. Log type errors, if any and wrap command exceptions
   * as domain check exceptions
   * @param sectName section name to type check
   * @throws DomainCheckException wrapped CommandException from type checking.
   */
  protected void typeCheck(String sectName) throws DomainCheckException
  {
    // attempt to typecheck the DC Z section, which should succeed.
    // raise a warning if it doesn't.
    try
    {
      // type check given spec? - if on-the-fly construction is wrong this will fail.
      sectManager_.get(new Key<SectTypeEnvAnn>(sectName, SectTypeEnvAnn.class));
    }
    catch (CommandException e)
    {
      if (e.getCause() != null)
      {
        final String msg = "Type error(s) in ZSect " + sectName
                           + "\n\t caused by " + e.getCause().getClass().getSimpleName()
                           + ": " + e.getCause().getMessage();
        logger_.warning(msg);
        if (e.getCause() instanceof TypeErrorException)
        {
          TypeErrorException typeErrorException = (TypeErrorException) e.getCause();
          final int i = printErrors(typeErrorException.getErrors());
          logger_.warning("DC-TYPECHK-ZSECT-ERROR = (" + sectName + ", " + i + ")");
        }
      }
      throw new DomainCheckException("DC-TYPECHK-ZSECT-ERROR = " + sectName, e);
    }
  }

  /* ZSect DC RESULTS CREATION METHODS */

  /**
   * Creates a ZSect header as "\SECTION sectName_dc \parents sectName" and empty paragraphs
   * @param sectName
   * @return
   */
  private ZSect createDCZSectHeader(String sectName)
  {
    ZSect result = factory_.createZSect(sectName + DOMAIN_CHECK_GENERAL_NAME_SUFFIX,
            factory_.list(factory_.createParent(sectName),
            factory_.createParent(DOMAIN_CHECK_TOOLKIT_NAME)),
            factory_.createZParaList());
    return result;
  }

  protected static final String ONTHEFLY_SCHEMA_NAME = "OnTheFlySchemaDC";
  protected static final String ONTHEFLY_ZSECT_NAME = "CZTtmpDCZSect";
  protected static int onTheFlySeed_ = 0;

  protected String createUniqueOnTheFlySchemaName()
  {
    String result = ONTHEFLY_SCHEMA_NAME + onTheFlySeed_;
    onTheFlySeed_++;
    return result;
  }

  protected String createUniqueDCZScectName()
  {
    String result = ONTHEFLY_ZSECT_NAME + onTheFlySeed_;
    onTheFlySeed_++;
    return result;
  }

  /**
   * Adds to the given Z section the list of domain check predicates for each
   * corresponding paragraph as a conjecture paragraph. It updates the Z section
   * result list of paragraphs, see {@link #ZSect.getZParaList()}. It also updates
   * the section manager information.
   * @param result Z section to add given list as conjectures; it is usually given empty.
   * @param dcList list of domain checks for each paragraph to be added to Z section result.
   * @throws DomainCheckException 
   */
  protected void populateResultsToDCZSect(ZSect result, List<Pair<Para, Pred>> dcList)
          throws DomainCheckException
  {
    assert result != null && dcList != null;

    // Add date it was created
    Date date = new Date();
    String narrText = "Created at " + date.toString() + ".\n\n";
    NarrPara narrPara = factory_.createNarrPara(factory_.list(narrText));
    result.getZParaList().add(narrPara);
    boolean addTrivialDC = isAddingTrivialDC();

    int dcCount = 0;
    // process each Para DC
    for (Pair<Para, Pred> pair : dcList)
    {
      Para para = pair.getFirst();
      Pred paraDC = pair.getSecond();

      //!addTrivialDC ==> !(paraDC instanceof TruePred)      
      if (addTrivialDC || !(paraDC instanceof TruePred))
      {
        // since we cannot retrieve the theorem's name from a latex, neither
        // generate it from a ConjPara, just add some NarrText around instead.
        narrText = "";

        // add location information
        LocAnn loc = para.getAnn(LocAnn.class);

        // try to add an offset to the toString print visitor
        try
        {
          ZUtils.assertZPrintVisitor(ZUtils.assertZTermImpl(loc).getFactory().getToStringVisitor()).setOffset(1, 1);
        }
        catch (UnsupportedAstClassException ast)
        {
          // fail silently if not possible.
          logger_.finest("DC-LOCANN-OFFSET-NOT-POSSIBLE");
        }
        if (loc != null)
        {
          narrText = "DC for " + loc.toString() + "\n";
        }
        else
        {
          narrText = "DC for " + para.toString() + "\n";
        }
        narrPara = factory_.createNarrPara(factory_.list(narrText));

        // retrieve genFormals in case of AxPara, or an empty list otherwise
        ZNameList genFormals = factory_.createZNameList();
        if (para instanceof AxPara)
        {
          genFormals.addAll(((AxPara) para).getZNameList());
        }
        ConjPara conjPara = factory_.createConjPara(genFormals, paraDC);

        // create the conjecture name or internal axiom name
        String conjName = null;
        int axiomCnt = 0;
        if (ZUtils.isAbbreviation(para))
        {
          conjName = ZUtils.assertZName(ZUtils.getAbbreviationName(para)).getWord();
        }
        else if (ZUtils.isSimpleSchema(para))
        {
          conjName = ZUtils.assertZName(ZUtils.getSchemaName(para)).getWord();
        }
        else if (para instanceof ConjPara)
        {
          conjName = ((ConjPara) para).getName();
        }
        else if (para instanceof FreePara)
        {
          // for multiple free types, just get the first name available.
          conjName = ZUtils.assertZFreetypeList(((FreePara) para).getFreetypeList()).get(0).getZName().getWord();
        }
        else if (para instanceof AxPara && ((AxPara) para).getBox().equals(Box.AxBox))
        {
          conjName = "axiom$" + axiomCnt;
          axiomCnt++;
        }

        // in any case, always have a name for it.
        if (conjName == null || conjName.isEmpty())
        {
          conjName = "dc$" + axiomCnt;
          axiomCnt++;
        }

        // add the conjecture name
        assert conjName != null && !conjName.isEmpty() : "Invalid conjecture name";
        ZName annName = factory_.createZName(conjName + DOMAIN_CHECK_CONJECTURE_NAME_SUFFIX);
        conjPara.getAnns().add(annName);
        //conjPara.setName(annName.getWord()); no need here ,since we create the ConjPara without ann        

        // add both narrative and dc conjecture paragraphs to the Z section result
        result.getZParaList().add(narrPara);
        result.getZParaList().add(conjPara);
        dcCount++;
      }
    }

    // add narrative para footer with the number of domain checks
    narrText = "Z section " + result.getName() + " has " + dcCount
               + (dcCount == 1 ? " DC" : "DCs") + ".\n";
    if (addTrivialDC && dcCount > 0)
    {
      narrText += "(of which " + (dcList.size() - dcCount) + " were trivial).\n";
    }
    narrText += "\n";
    narrPara = factory_.createNarrPara(factory_.list(narrText));
    result.getZParaList().add(narrPara);   
  }

  /**
   * Domain checks the given Z section. The result is a Z sections with the
   * given Z section as its parent, and with domain check conjectures for
   * all its paragraphs.
   *
   * @param term Z section to domain check
   * @return DC Z section as a list of domain check conjectures
   * @throws DomainCheckException
   */
  protected ZSectDCEnvAnn createZSectDCEnvAnn(ZSect term)
          throws DomainCheckException
  {
    assert term != null;
    String sectName = term.getName();
    checkSectionManager(sectName);

    // create section header: \SECTION sectName_dc \parents sectName
    ZSect zsectDC = createDCZSectHeader(sectName);
    String sectNameDC = zsectDC.getName();

    // domain check sectName
    List<Pair<Para, Pred>> dcList = dc(term);

    // update the zsectDC and add it to the SectionManager
    // it is accessible as manager.get(new Key<ZSect>(sectName + DOMAIN_CHECK_GENERAL_NAME_SUFFIX, ZSect.class));
    populateResultsToDCZSect(zsectDC, dcList);

    // update section manager with calculated results:
    // (e.g., put DC ZSect as well as Op/Thm tables
    updateManager(zsectDC);

    // type check DC Z section just created on the fly - it ought to succeed
    typeCheck(sectNameDC);

    // attempt to collect the ThmTable for the DC Z section = double checking updateManager worked. TODO: remove? yes?
    try
    {
      // ask section manager to calculate ThmTable for new DC ZSect
      // it updates the manager as well.
      sectManager_.get(new Key<ThmTable>(sectNameDC, ThmTable.class));
    }
    catch (CommandException ex)
    {
      throw new DomainCheckException("DC-CREATE-ZSectDC = could not create ThmTable for " + sectNameDC, ex);
    }

    // create a ZSectDCEnvAnn with the original section name where
    // the dcList is associated with.
    ZSectDCEnvAnn result = new ZSectDCEnvAnn(sectName, dcList);
    return result;
  }

  // CREATES ZSectDCEnvAnn for ZSect, Para, Pred, Expr, or Decl
  /**
   * Domain checks the given term, presuming it is a ZSect, Para, Pred,
   * Expr or Decl. The result is Z sections named uniquely with
   * standard and dc toolkits as its parents, and with domain check
   * conjectures for the term, if any. The result is a wrapped ZSectDCEnvAnn.
   *
   * @param term Z section to domain check
   * @return DC Z section as a list of domain check conjectures
   * @throws DomainCheckException
   */
  public ZSectDCEnvAnn createZSectDCEnvAnn(Term term)
          throws DomainCheckException
  {
    assert term != null : "invalid general term to domain check";
    // make sure DC is properly configured
    final String msg = "for term " + term.getClass().getSimpleName();
    checkSectionManager(msg);

    Para para;
    Factory factory = getZFactory();
    if (term instanceof ZSect)
    {
      return createZSectDCEnvAnn((ZSect) term);
    }
    else if (term instanceof Para)
    {
      para = (Para) term;
    }
    else
    {
      // for everything else, create a schema text
      ZSchText zSchText;
      if (term instanceof Pred)
      {
        // [ | pred ]
        zSchText = factory.createZSchText(factory.createZDeclList(), (Pred) term);
      }
      else if (term instanceof Expr)
      {
        // [ | pred(Expr) ]
        zSchText = factory.createZSchText(factory.createZDeclList(), factory.createExprPred((Expr) term));
      }
      else if (term instanceof Decl)
      {
        // [ Decl | true ]
        zSchText = factory.createZSchText(factory.createZDeclList(
                factory.list((Decl) term)), factory.createTruePred());
      }
      else
      {
        // cannot be processed, raise exception
        throw new DomainCheckException("Invalid general term to domain check. It must be either "
                                       + "a paragraph, a declaration, a predicate, or an expression, yet a " + term.getClass().getName() + " was given.");
      }
      // make it a schema named internally and uniquely
      assert zSchText != null;
      para = factory.createSchema(factory.createZName(createUniqueOnTheFlySchemaName()), zSchText);
    }
    assert para != null;

    // create an empty section header: that is, wrap the term as a ZSect inheriting std_toolkit
    ZSect zsect = factory.createZSect(createUniqueDCZScectName(),
            factory.list(factory.createParent("standard_toolkit")),
            factory.createZParaList());
    zsect.getZParaList().add(para);

    // domain check on-the-fly Z section with std_toolkit as parent
    ZSectDCEnvAnn result = createZSectDCEnvAnn(zsect);
    return result;
  }

  //  // CREATES List<ZSectDCEnvAnn> for each Spec ZSect
//  /**
//   * Domain checks all Z sections within the given specification term.
//   * The result are children Z sections with the corresponding spec Z section
//   * as its parent, and with domain check conjectures for all its paragraphs.
//   *
//   * @param term specification to domain check
//   * @return list of DC Z section as a list of domain check conjectures
//   * @throws DomainCheckException
//   */
//  private List<ZSectDCEnvAnn> createZSectDCEnvAnn(Spec term)
//          throws DomainCheckException
//  {
//    // presumes section manager has been configured
//    checkSectionManager("");
//
//    // calculate the DC map for each ZSect within Spec term
//    SortedMap<String, List<Pair<Para, Pred>>> dcMap = dc(term);
//
//    // for each ZSect, create a DC ZSect child with the DC elements.
//    List<ZSectDCEnvAnn> result = new ArrayList<ZSectDCEnvAnn>(dcMap.size());
//    for (Map.Entry<String, List<Pair<Para, Pred>>> entry : dcMap.entrySet())
//    {
//      // create a bare ZSect header
//      String originalZSectName = entry.getKey();
//      ZSect zsect = createDCZSectHeader(originalZSectName);
//      List<Pair<Para, Pred>> dcs = entry.getValue();
//
//      // update the paragraphs of DC Z Sect with DC conjectures
//      populateResultsToDCZSect(zsect, dcs);
//
//      ZSect original = ZUtils.retrieveZSect(term, originalZSectName);
//      assert original != null;
//
//      // update the result
//      result.add(new ZSectDCEnvAnn(originalZSectName, dcs));
//    }
//
//        assert sectManager_ != null;
//        sectManager_.put(new Key<ZSect>(sectName + DOMAIN_CHECK_GENERAL_NAME_SUFFIX, result);/
//
//
//    // ensure result is consistent with collected info
//    assert result.size() == dcMap.size() : "More DC's for mapped section than resulting List<ZSecT>!";
//
//    return result;
//  }

//  /**
//   * Domain checks all Z sections within the given specification term.
//   * The result are children Z sections with the corresponding spec Z section
//   * as its parent, and with domain check conjectures for all its paragraphs.
//   * This is a convenience method that relies on the result of {@link #createZSectDCEnvAnn(Spec, boolean, boolean)}.
//   * The <code>specKey</code> parameter is necessary in order to update the section manager with
//   * the DC Spec created by this method.
//   *
//   * @param specKey section manager key associated with Spec?
//   * @param term specification to domain check
//   * @return list of DC Z section as a list of domain check conjectures
//   * @throws DomainCheckException
//   */
//  public SpecDCEnvAnn createSpecDCEnvAnn(Spec term) throws DomainCheckException
//  {
//    // populate the term with its DC Z Sect children
//    List<ZSectDCEnvAnn> sects = createZSectDCEnvAnn(term);
//
//    // create an empty Spec
//    Spec dcSpec = factory_.createSpec(factory_.<ZSect>list(), term.getVersion());
//
//    // Add header for date it was created
//    Date date = new Date();
//    String narrText = "Domain checked specification created at " + date.toString() + ".\n\n";
//    NarrSect header = factory_.createNarrSect(factory_.<String>list(narrText));
//    dcSpec.getSect().add(header);
//
//    // populate the spec with each DC Z Sect child
//    for (ZSectDCEnvAnn zsDCEnvAnn : sects)
//    {
//      dcSpec.getSect().add(zsDCEnvAnn.getDCZSect(sectInfo_));
//    }
//
//    // update section manager with DC Z Spec information, with dependencies to given Spec
//    // if this term is known within the section manager.
//    Key<Spec> specKey = sectInfo_.retrieveKey(term);
//    String specKeyName = "Specification"; // a general resource name
//    if (specKey != null)
//    {
//      specKeyName = specKey.getName();
//      Key<Spec> dcSpecKey = new Key<Spec>(specKeyName + DOMAIN_CHECK_GENERAL_NAME_SUFFIX, Spec.class);
//      sectInfo_.put(dcSpecKey, dcSpec, new HashSet<Key<?>>(Collections.singleton(specKey)));
//    }
//
//    // wrap the result to be returned - may have a null specKeyName
//    SpecDCEnvAnn result = new SpecDCEnvAnn(specKeyName, sects);
//    return result;
//  }
}
