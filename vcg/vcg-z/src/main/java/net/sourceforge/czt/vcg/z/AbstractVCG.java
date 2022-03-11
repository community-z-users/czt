/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.vcg.z;

import java.io.File;
import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.logging.Level;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.parser.util.ThmTable;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.vcg.util.DefaultVCNameFactory;
import net.sourceforge.czt.vcg.util.DefinitionException;
import net.sourceforge.czt.vcg.util.DefinitionTable;
import net.sourceforge.czt.vcg.util.DefinitionTableService;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameList;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
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
 * Base class for all VCG utility classes. It can process Terms for VCG, where
 * the return is a list of R, which is usually Para/VC pairs.
 *
 * @param <T> subtype of Type2 determining the kind VCContext for VCs being generated as Pred
 * @param <B> kind of bindinds to consider from VCContext (i.e. FSB or RREF, see VCContext)
 * @author Leo Freitas
 * @date Dec 23, 2010
 */
//* param <R> usually instantiated as of paragraph / predicate pairs.
public abstract class AbstractVCG<//R, 
									T, B>
        implements VCGPropertyKeys, 
        ParaVisitor<List<VC<Pred>>>,//<List<VC<R>>>,
        ParentVisitor<List<VC<Pred>>>,
        SectVisitor<List<VC<Pred>>>,
        ZSectVisitor<List<VC<Pred>>>,
        VCG<//R, 
        		T, B>
{
  /**
   * Prefixes for named terms created during VC processing.
   */
  protected static final String ONTHEFLY_SCHEMA_NAME = "OnTheFlySchemaVC$";
  protected static final String ONTHEFLY_ZSECT_NAME = "CZTtmpVCZSect$";
  static int onTheFlyNamesSeed_ = 0;

  /**
   * Flag for adding or not trivial VCs (i.e. those that are tantamount to true like (true or a)).
   * Each VCG extension has a predicate transformer class that simplifies/normalises the predicates.
   * For a strict set of VCs keep addTrivialVC on.
   */
  private boolean addTrivialVC_;
  
  /**
   * When generating VCs the VCG typechecks the new Z Section created. In some (complex) cases
   * (e.g. involving generic types) VCs might not typecheck, although this is easily fixed manually.
   * This flag controls whether or not 
   */
  private boolean logTypeWarnings_;
  
  /**
   * When generating VCs the VCG determine whether or not to process section parents for VCs depending
   * on this flag. In many cases this is important, like in user defined section hierarchies. In other
   * cases, like in standard toolkits, this is a waste to work and can be avoided.
   */
  private boolean processParents_;
  
  /**
   * Low-level flag determining whether the VCG is properly configured or not. This involves determining
   * what kind of VC collector to use, attaching a section manager, adjust default properties according
   * to user defined section manager properties, etc. The method isConfigured() does more than this low-level
   * flag in the sense that it checks for collector and section manager as well. The method config() setup
   * the VCG, whereas doConfig() is used by descending classes.
   */
  private boolean isConfigured_;
  
  /**
   * Set of section parents to ignore by default. Even if processParents_ is true, parents on this set
   * are ignored. Usually they contain known / stable sections like toolkits.
   */
  private SortedSet<String> parentsToIgnore_;

  /**
   * Flag determining whether or not to run a (memory expensive) check on the bindings of the definition table 
   * created. It is useful to keep it on when dealing with more complicated specifications where the schema
   * calculus might not have been fully covered yet. 
   */
  private boolean checkTblConsistency_;

  /**
   * Definition table for the current section. This is the extended Definition table from the VCG project,
   * rather than the usual/default one from the parser-z project. It includes complex calculation of bindings.
   */
  private DefinitionTable defTable_;
  
  /**
   * Operator table for the current section.
   */
  private OpTable opTable_;
  
  /**
   * Section manager used by this VCG.
   */
  private SectionManager sectManager_;
  
  /**
   * Factory used by the VCG to create new VC predicates
   */
  private final Factory factory_;
  
  /**
   * Logger used to report errors and warnings.
   */
  private final Logger logger_;
  
  /* CLASS SETUP AND FIELD ACCESS METHODS */

  /**
   * Creates a default VCG using a Z console factory (i.e. it produces console-friendly printouts of Logger messages).
   */
  protected AbstractVCG()
  {
    this(ZUtils.createConsoleFactory());
  }

  /**
   * Creates a VCG with the given factory. This will be used to create all predicates within the VC collector.
   * Different Z extensions can use different factories accordingly. Factory cannot be null.
   * @param factory to create VC terms.
   */
  protected AbstractVCG(Factory factory)
  {
    if (factory == null)
    {
      throw new IllegalArgumentException("VCG-TERM-NULL-FACTORY");
    }
    factory_ = factory;
    logger_ = Logger.getLogger(getClass().getName());
    
    isConfigured_ = false;
    opTable_ = null;
    defTable_ = null;
    sectManager_ = null;
    addTrivialVC_    = PROP_VCG_ADD_TRIVIAL_VC_DEFAULT;
    logTypeWarnings_ = PROP_VCG_RAISE_TYPE_WARNINGS_DEFAULT;
    processParents_  = PROP_VCG_PROCESS_PARENTS_DEFAULT;
    checkTblConsistency_ = PROP_VCG_CHECK_DEFTBL_CONSISTENCY_DEFAULT;
    parentsToIgnore_ = new TreeSet<String>();
  }

  protected Logger getLogger()
  {
    return logger_;
  }
  
  protected Factory getFactory()
  {
    return factory_;
  }
  
  protected OpTable getOpTable()
  {
    return opTable_;
  }
  
  protected boolean defaultAddTrivialVC()
  {
    return PROP_VCG_ADD_TRIVIAL_VC_DEFAULT;
  }

  protected boolean defaultRaiseTypeWarnings()
  {
    return PROP_VCG_RAISE_TYPE_WARNINGS_DEFAULT;
  }

  protected boolean defaultProcessParents()
  {
    return PROP_VCG_PROCESS_PARENTS_DEFAULT;
  }

  protected boolean defaultApplyTransformers()
  {
    return PROP_VCG_APPLY_TRANSFORMERS_DEFAULT;
  }

  protected boolean defaultCheckDefTblConsistency()
  {
    return PROP_VCG_CHECK_DEFTBL_CONSISTENCY_DEFAULT;
  }

  /**
   * By default ignore all STANDARD_TOOLKIT_NAMES and EXTENDED_TOOLKIT_NAMES Z sections.
   * Extending classes should inherit this method to add more.
   * @return default set of parents to ignore
   */
  protected SortedSet<String> defaultParentsToIgnore()
  {
    SortedSet<String> result = new TreeSet<String>(Section.standardSections());//Arrays.asList(STANDARD_TOOLKIT_NAMES));
    //result.addAll(Arrays.asList(EXTENDED_TOOLKIT_NAMES));
    return result;
  }

  /* CLASS VCG interface methods */
  /**
   * True whenever section manager and VC collectors are not null, if the
   * configuration flag is set as well.
   * @return sectManager_ != null &amp;&amp; getVCCollector() != null &amp;&amp; isConfigured_
   */
  @Override
  public boolean isConfigured()
  {
    return sectManager_ != null && getVCCollector() != null && isConfigured_;
  }

  /**
   *
   * @return
   */
  //@Override
  //public abstract VCCollector<//R, 
  //								T, B> getVCCollector();

  @Override
  public SectionManager getManager()
  {
    return sectManager_;
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
  @Override
  public void addParentSectionToIgnore(String parent)
  {
    assert parent != null && !parent.isEmpty() : "Invalid (null or empty) section name.";
    parentsToIgnore_.add(parent);
  }

  /**
   * Returns a unmodifiable set of section names not being processed for VC generation.
   * @return
   */
  @Override
  public SortedSet<String> getParentsToIgnore()
  {
    return Collections.unmodifiableSortedSet(parentsToIgnore_);
  }

  @Override
  public boolean isAddingTrivialVC()
  {
    return addTrivialVC_;
  }

  @Override
  public boolean isProcessingParents()
  {
    return processParents_;
  }

  @Override
  public boolean isRaisingTypeWarnings()
  {
    return logTypeWarnings_;
  }

  @Override
  public boolean isCheckingDefTblConsistency()
  {
    return checkTblConsistency_;
  }

  /**
   * Clears both sets of parents to process and to ignore
   */
  /**
   * Clears both sets of parents to process and to ignore
   */
  public void clearParentsToIgnore()
  {
    parentsToIgnore_.clear();
  }

  /**
   * These methods sets various flags for the VCG. It is important to note that
   * they are set during configuration to either defaults or section manager's values.
   * So, to have any effect, they need to be set after configuration, see {@link #config()}.
   * @param value
   */
  public void setAddingTrivialVC(boolean value)
  {
    addTrivialVC_ = value;
  }

  public void setCheckDefTblConsistency(boolean value)
  {
    checkTblConsistency_ = value;
  }

  public void setProcessingParents(boolean value)
  {
    processParents_ = value;
  }

  public void setRaiseTypeWarnings(boolean value)
  {
    logTypeWarnings_ = value;
  }

  /**
   * Reset parameters, sets the section manager, then retrieves configuration for
   * known properties (i.e., it calls {@link #reset()} and {@link #config()} methods).
   * @param manager non-null manager
   * @throws VCGException
   */
  @Override
  public void setSectionManager(SectionManager manager) throws VCGException
  {
    if (manager == null)
    {
      throw new VCGException(getDialect(), "VCG-SM-NULL");
    }
    else /*if (sectManager_ != manager)  in case properties change */
    {
      reset();
      sectManager_ = manager;
      config();
    }
  }
  
  protected Dialect getDialect()
  {
	  if (sectManager_ != null) 
		  return sectManager_.getDialect();
	  else
		  return Dialect.Z;
  }

  /* VCG CONFIGURATION METHODS */

   /**
   * Checks whether there is a section manager or not, and raises the error
   * wrapped up as a CztException.
   * @param info some data, usually ZSect Name, say
   * @throws VCGException  if there is no section manager
   */
  protected void checkSectionManager(String info) throws VCGException
  {
    if (sectManager_ == null)
    {
      final String msg = "VCG-PROCESS-ERROR = No SectMngr! " + info;
      getLogger().severe(msg);
      throw new VCGException(getDialect(), msg);
    }
  }

  /**
   * Sets up available options according to the section manager's configuration.
   * It does nothing if no section manager is available.
   * @return underlying section manager properly configured, if needed (see {@link #isConfigured() }).
   * @throws VCGException
   */
  @Override
  public final SectionManager config() throws VCGException
  {
    checkSectionManager("VCG-NO-SM = use default options");

    // use the flag only here, since the method checks for the manager and collector as well.
    if (!isConfigured_)//!isConfigured())
    {
      boolean processParents = sectManager_.hasProperty(PROP_VCG_PROCESS_PARENTS) ?
        sectManager_.getBooleanProperty(PROP_VCG_PROCESS_PARENTS) : defaultProcessParents();
      boolean addTrivialVC = sectManager_.hasProperty(PROP_VCG_ADD_TRIVIAL_VC) ?
        sectManager_.getBooleanProperty(PROP_VCG_ADD_TRIVIAL_VC) : defaultAddTrivialVC();
      boolean raiseTW = sectManager_.hasProperty(PROP_VCG_RAISE_TYPE_WARNINGS) ?
        sectManager_.getBooleanProperty(PROP_VCG_RAISE_TYPE_WARNINGS) : defaultRaiseTypeWarnings();
      boolean applyTransf = sectManager_.hasProperty(PROP_VCG_APPLY_TRANSFORMERS) ?
        sectManager_.getBooleanProperty(PROP_VCG_APPLY_TRANSFORMERS) : defaultApplyTransformers();
      boolean checkTblConst = sectManager_.hasProperty(PROP_VCG_CHECK_DEFTBL_CONSISTENCY) ?
        sectManager_.getBooleanProperty(PROP_VCG_CHECK_DEFTBL_CONSISTENCY) : defaultCheckDefTblConsistency();
      List<String> parentsToIgnore = sectManager_.hasProperty(PROP_VCG_PARENTS_TO_IGNORE) ?
        sectManager_.getListProperty(PROP_VCG_PARENTS_TO_IGNORE) :
        new ArrayList<String>(defaultParentsToIgnore());
      setProcessingParents(processParents);
      setAddingTrivialVC(addTrivialVC);
      setRaiseTypeWarnings(raiseTW);
      setCheckDefTblConsistency(checkTblConst);
      clearParentsToIgnore();
      parentsToIgnore_.addAll(parentsToIgnore);

      if (getVCCollector() == null)
      {
        throw new VCGException(getDialect(), "VCG-CONFIG-NULL-VC-COLLECTOR");
      }
      else if (getVCCollector().getTransformer() == null)
      {
    	throw new VCGException(getDialect(), "VCG-CONFIG-NULL-VC-COLLECTOR-TRANSFORMER");  
      }
      else if (getVCCollector().getVCGContext() == null)
      {
      	getLogger().severe("TODO: Add VCG Context to configuration");
    	//throw new VCGException("VCG-CONFIG-NULL-VC-COLLECTOR-VCG-CONTEXT");
      }
      getVCCollector().getTransformer().setApplyTransformer(applyTransf);

      assert sectManager_ != null;
      // override the Z DefTable cmd: use more advanced VCG definition table algorithm
      sectManager_.putCommand(DefinitionTable.class, DefinitionTableService.getCommand(sectManager_));

      doConfig();
      
      isConfigured_ = true;
      getLogger().config("VCG-SM = load SM options");
    }

    return sectManager_;
  }

  protected void doConfig() throws VCGException
  {
    assert sectManager_ != null && !isConfigured_;

    // make sure all visiting is at least accounted for - kinda of redundant but leave it
    // (e.g., could remove after impl is more mature)
    //VisitorUtils.checkVisitorRules(this);
    //VisitorUtils.checkVisitorRules(getVCCollector());
    //VisitorUtils.checkVisitorRules(getVCCollector().getTransformer().getTermVisitor());
  }

  @Override
  public final void setDefaultProperties(SectionManager manager)
  {
    if (manager == null)
      getLogger().warning("VCG-DEFPROP-NULL-SM");
    else
    {
      manager.setProperty(PROP_VCG_PROCESS_PARENTS, String.valueOf(defaultProcessParents()));
      manager.setProperty(PROP_VCG_ADD_TRIVIAL_VC, String.valueOf(defaultAddTrivialVC()));
      manager.setProperty(PROP_VCG_APPLY_TRANSFORMERS, String.valueOf(defaultApplyTransformers()));
      manager.setProperty(PROP_VCG_RAISE_TYPE_WARNINGS, String.valueOf(defaultRaiseTypeWarnings()));
      manager.setProperty(PROP_VCG_CHECK_DEFTBL_CONSISTENCY,
            String.valueOf(defaultCheckDefTblConsistency()));

      // build it from parents to ignore
      StringBuilder prop = new StringBuilder();
      for (String path : defaultParentsToIgnore())
      {
        prop.append(path);
        prop.append(File.pathSeparator);
      }
      String propS = prop.toString();
      if (prop.length() > 0)//!prop.isEmpty())
      {
        propS = prop.substring(0, prop.lastIndexOf(File.pathSeparator));
      }
      manager.setProperty(PROP_VCG_PARENTS_TO_IGNORE, propS);

      doDefaultProperties(manager);
    }
  }

  protected void doDefaultProperties(SectionManager manager)
  {
    assert manager != null;
    // do nothing - for derived classes use.
  }


  /**
   * Resets the VCG fields and section manager.
   */
  @Override
  public void reset()
  {
    sectManager_ = null;
    clearNecessaryTables();
    addTrivialVC_ = defaultAddTrivialVC();
    logTypeWarnings_ = defaultRaiseTypeWarnings();
    processParents_ = defaultProcessParents();
    checkTblConsistency_ = defaultCheckDefTblConsistency();
    getVCCollector().getTransformer().setApplyTransformer(defaultApplyTransformers());
    clearParentsToIgnore();
    parentsToIgnore_.addAll(defaultParentsToIgnore());
    isConfigured_ = false;
  }


  /* AUXILIARY VC CALCULATION METHODS */

  protected String createUniqueName(String prefix)
  {
    final String result = prefix + onTheFlyNamesSeed_;
    onTheFlyNamesSeed_++;
    return result;
  }

  protected String createUniqueOnTheFlySchemaName()
  {
    return createUniqueName(ONTHEFLY_SCHEMA_NAME);
  }

  protected String createUniqueZScectName()
  {
    return createUniqueName(ONTHEFLY_ZSECT_NAME);
  }

  /**
   * Type checks the given section name. Log type errors, if any and 
   * wrap command exceptions as VCG exceptions. Override this if your
   * VCG shouldn't raise a type error for some reason - do it by capturing
   * the VCGException with a TypeErrorException cause.
   * @param sectName section name to type check
   * @param sourceSect  true if the typechecked section is a source section, false if it is the VC section
   * @throws VCGException wrapped CommandException from type checking.
   */
  @Override
  public void typeCheck(String sectName, boolean sourceSect) throws VCGException
  {
	checkSectionManager("VCG-TYPECHECK-ZSECT " + sectName);
	
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
        final String msg = "VCG-ZSECT-RES-TYPE-ERRORS = " + sectName
                + "\n\t caused by " + e.getCause().getClass().getSimpleName()
                + ": " + e.getCause().getMessage();
        getLogger().warning(msg);
        if (e.getCause() instanceof TypeErrorException)
        {
          TypeErrorException typeErrorException = (TypeErrorException) e.getCause();
          final int i = printTypeErrors(typeErrorException.getErrors());
          getLogger().log(Level.WARNING, "VCG-TYPECHK-ZSECT-ERROR = ({0}, {1})", new Object[]{sectName, i});
        }
      }
      throw new VCGException(getDialect(), "VCG-TYPECHK-ZSECT-ERROR = ", sectName, e);
    }
  }

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
  protected int printTypeErrors(List<? extends ErrorAnn> errors)
  {
    int result = 0;
    //print any errors
    for (ErrorAnn next : errors)
    {
      // raiseWarnings => next.getErrorType(ErrorType.ERROR) only
      if (isRaisingTypeWarnings() || next.getErrorType().equals(ErrorType.ERROR))
      {
        // TODO: fix this? It might generate section management problems in case of
        //       systemic management error / failure :-( = toString uses the SectionManager
        getLogger().warning(next.toString());
        result++;
      }
    }
    return result;
  }

  protected List<String> printTypeErrors(TypeErrorException tee)
  {
    List<String> result = new ArrayList<String>();
    //print any errors
    for (ErrorAnn next : tee.getErrors())
    {
    	// raiseWarnings => next.getErrorType(ErrorType.ERROR) only
        if (isRaisingTypeWarnings() || next.getErrorType().equals(ErrorType.ERROR))
        {
        	result.add(next.toString());
        }
    }
    return result;
  }

  /**
   * Calculate ThmTable for the VC ZSectName create on the fly
   * @param sectNameVC
   * @throws VCGException
   */
  protected void calculateThmTable(String sectNameVC) throws VCGException
  {
	checkSectionManager("VCG-THMTABLE-ZSECT-VC " + sectNameVC);
	  
    // attempt to collect the ThmTable for the Z section
    try
    {
      // ask section manager to calculate ThmTable for new VC ZSect. it updates the manager as well.
      sectManager_.get(new Key<ThmTable>(sectNameVC, ThmTable.class));
    }
    catch (CommandException ex)
    {
      throw new VCGException(getDialect(), "VCG-CREATE-ZSectDC = could not create ThmTable for ", sectNameVC, ex);
    }
  }

  /* VC CALCULATION TERM VISITING METHODS */

  /* NOTE: although some of these methods are public, they are NOT top-level and
           should only be called by derived, not utility/user, classes. */

  /**
   * Collect all DC predicates from the terms within the given list.
   * This could be a ZParaList, a ListTerm<Parent>, or ListTerm<Sect>,
   * which comes from ZSect.getZParaList(), ZSect.getParent(), and
   * Spec.getSect().
   * @param <M>
   * @param list
   * @return
   */
  protected final <M extends Term> /*List<Pair<Para, Pred>>*/ List<VC<Pred>> collect(@SuppressWarnings("unchecked") M... list)
  {
    /*List<Pair<Para, Pred>> result = factory_.list();*/
    List<VC<Pred>> result = factory_.list();
    for (M term : list)
    {
      result.addAll(visit(term));
    }
    return result;
  }

  /**
   * Visits the given term (e.g., <code>term.accept(this)</code>).
   * AbstractVCG only takes care of top-level term structures,
   * which MUST NOT be null ! If null, a proper exception is raised.
   * @param term term to visit
   */
  protected List<VC<Pred>> visit(Term term)
  {
    if (term == null)
      throw new CztException(new VCGException(getDialect(), "VCG-VISIT-TOPLEVEL-NULL-TERM"));
    return term.accept(this);
  }

  /**
   * Class used in section management keys. It determines the kind of VCEnvAnn class
   * to query/update the section manager with. For instance, for domain checking,
   * the result should be a DCVCEnvAnn class.
   * @return class for the kind of section management key to use.
   */
  //@Override
  //public abstract Class<? extends VCEnvAnn> getVCEnvAnnClass();

  /**
   *
   * @param <K>
   * @param originalZSectName
   * @param type
   * @return
   */
  private <K> Key<K> createSMKey(String originalZSectName, Class<K> type)
  {
    return new Key<K>(originalZSectName, type);
  }

  /**
   * CZT visiting does not allow specific Exceptions (unfortunately - this is because
   * generic types were not available then). So, we need to wrap any VCGException under CztException.
   * Top-level methods MUST capture these and raise the VCGException appropriately.
   * (see {@link #vcsOf(net.sourceforge.czt.z.ast.ZSect) }.
   * @param msg
   */
  protected void raiseVCGExceptionWhilstVisiting(final String msg, Throwable cause)
  {
    getLogger().warning(msg);
    throw new CztException(new VCGException(getDialect(), msg, cause));
  }

  protected abstract boolean isTableMandatory(Key<? extends InfoTable> key);
  protected abstract boolean shouldTryTableAgain(Key<? extends InfoTable> key);


  /**
   * Retrieves any necessary section manager information like definition and operator tables.
   * Other tables might be configured at this point by derived classes. This is called right
   * before visiting a ZSect. It requires a configured section manager. 
   * 
   * Table calculation is expensive, hence we keep it at higher level in the hierarchy (i.e.
   * not per VC but per VCG-processed section session). Sometimes (i.e. because not yet calculated/
   * parsed section), it's necessary to try again. More than twice failure is unrecoverable. We
   * use the flags from the methods shouldTryAgain() to see whether to try or not.
   *
   * @param sect
   */
  protected void retrieveTables(ZSect sect)
  {
    //checkSectionManager("VCG-RETRIVE-TBLS- " + sectName); - assume it will be; assert it below.
    assert isConfigured();

    String sectName = sect.getName();
    
    DefinitionTable defTbl = null;
    Key<DefinitionTable> defTblKey = new Key<DefinitionTable>(sectName, DefinitionTable.class);
    // attempt retrieving defintion + operator tables.
    try
    {
      // retrieve definition + operator tables for Z section being analysed
      defTbl = sectManager_.get(defTblKey);
    }
    catch (CommandException e)
    {
      // if this table is mandatory, process the failures
      if (isTableMandatory(defTblKey))
      {
        // if should try again, then do so
        if (shouldTryTableAgain(defTblKey))
        {
          try
          {
            // try again = will get the partial/not-up-to-date deftable = one more chance.
            if (e instanceof DefinitionException)
            {
              //getLogger().warning("VCG-DEFTBL-ZSECT-ERROR(1st time) = " + sectName + " \n\t" + e.getMessage());
              defTbl = sectManager_.get(new Key<DefinitionTable>(sectName, DefinitionTable.class));
            }
            else
            {
              raiseVCGExceptionWhilstVisiting("VCG-VISIT-ZSECT-ERROR(1st time) = CmdExpt @ DefTable for: " + sectName
                    /*+ "(i.e., can only use AppliesTo rather than \\dom)." + "\n\t " +*/, e/*.getMessage()*/);
            }
          }
          catch (CommandException f)
          {
            resetDefTable();
            //if (e instanceof DefinitionException)
            //{
            //  getLogger().warning("VCG-DEFTBL-ZSECT-ERROR(2nd time) = " + sectName +
            //          "\n\t " + f.getMessage());
            //}
            //else
            //{
              raiseVCGExceptionWhilstVisiting("VCG-VISIT-ZSECT-ERROR(2nd time) = CmdExpt @ DefTable for: " + sectName
                   /*+ "(i.e., can only use AppliesTo rather than \\dom)." + "\n\t " +*/, f/*.getMessage()*/);
            //}
          }
        }
        // otherwise, raise the error
        else
        {
          raiseVCGExceptionWhilstVisiting("VCG-VISIT-ZSECT-ERROR(only-time) = CmdExpt @ DefTable for: " + sectName, e);
        }
      }
      // otherwise, carry on silently
    }
    Key<OpTable> opTblKey = new Key<OpTable>(sectName, OpTable.class);
    OpTable opTbl = null;
    try
    {
      opTbl = sectManager_.get(opTblKey);
    }
    catch (CommandException e)
    {
      opTbl = null;
      if (isTableMandatory(opTblKey))
      {
        raiseVCGExceptionWhilstVisiting("VCG-VISIT-ZSECT-ERROR = CmdExpt @ OpTable for: " + sectName,
              /*+ "\n\t " + */ e /*.getMessage()*/);
      }
    }
    try
    {
      beforeCalculateVC(sect, Arrays.asList(defTbl, opTbl));
    }
    catch(VCCollectionException e)
    {
      clearNecessaryTables();
      raiseVCGExceptionWhilstVisiting("VCG-VISIT-ZSECT-ERROR = setting tables for: " + sectName, e);
    }
  }
  
  protected void retrieveVCGContext(ZSect term)
  {
	  // populate the VCG Context with the given term meta-paragraphs if any
	  //throw new UnsupportedOperationException();
	  getLogger().severe("TODO: populate VCG context");
  }
  
  protected static OpTable checkOpTableWithinListIfNeeded(List<? extends InfoTable> tables, boolean checkConsistency)
		  throws VCCollectionException
  {
	  OpTable result = null;
	  for (InfoTable t : tables)
	  {
		  if (t instanceof OpTable)
		  {
			  result = (OpTable)t;
			  if (checkConsistency)
			  {
				  // do something here...
			  }
		  }
	  }
	  return result;
  }
  
  protected void beforeCalculateVC(ZSect term, List<? extends InfoTable> tables)
      throws VCCollectionException
  {
    defTable_ = AbstractVCCollector.checkDefinitionTableWithinListIfNeeded(tables, checkTblConsistency_);
    opTable_ = checkOpTableWithinListIfNeeded(tables, checkTblConsistency_);
  }
  
  protected void resetDefTable()
  {
    defTable_ = null;
  }

  /**
   *
   */
  protected void clearNecessaryTables()
  {
    resetDefTable();
    opTable_ = null;
  }

  protected List<? extends InfoTable> getAvailableSMTables()
  {
    List<InfoTable> result = factory_.list();
    if (defTable_ != null)
      result.add(defTable_);
    if (opTable_ != null)
      result.add(opTable_);
    return result;
  }
  
  /**
   * Retrieves for the given paragraph a corresponding VC
   * based over information on the current definition table.
   *
   * @param term
   * @return
   */
  @Override
  public List<VC<Pred>> visitPara(Para term)
  {
    List<VC<Pred>> result = factory_.list();
    
    // checkSectionManager(sectName); - assume it will be in place
    assert isConfigured();

    // the meta-model paragraphs are not processed for VC calculation.
    if (getVCCollector().getVCGContext() == null)
    	getLogger().severe("TODO: VCG CONTEXT IS NULL!");
    else
    if (!getVCCollector().getVCGContext().isVCGContextPara(term))
    {
	    // collect VCs for the given ZSect paragraph. any tables available can be used.
	    // VCCollection exceptions are wrapped as CztError because of visiting protocol.
	    // method vcsOf will throw then appropriately
	    VC<Pred> vc;
	    try
	    {
	      // available tables must have been already calculated earlier. Otherwise, no tables returned.
	      vc = getVCCollector().calculateVC(term, getAvailableSMTables());
	    }
	    catch (VCCollectionException ex)
	    {
	      throw new CztException(ex);
	    }
	    result.add(vc);
    }
    return result;
  }

  /**
   * For parent sections, calculate their dependent ZSect VCs by looking up the section manager,
   * unless this parent is set to be ignored (see {@link #getParentsToIgnore() }).
   * @param term
   * @return
   */
  @Override
  public List<VC<Pred>> visitParent(Parent term)
  {
    String sectName = term.getWord();
    // if this is one known parent to ignore, raise an error
    if (parentsToIgnore_.contains(sectName))
    {
      final String msg = "VCG-IGNORE-PARENT = " + sectName;
      getLogger().info(msg);
    }
    else
    {
      // checkSectionManager(sectName); - assume it will be in place
      assert isConfigured();
      try
      {
        // calculate the VCs for the given section using VCGCommand. this updates the
        // section manager to contain the appropriate parent information.
        VCEnvAnn zsVCEnvAnn = sectManager_.get(createSMKey(sectName, getVCEnvAnnClass()));
        assert zsVCEnvAnn != null;
      }
      catch (CommandException ex)
      {
        raiseVCGExceptionWhilstVisiting("VCG-VISIT-PARENT-ERROR = CmdExpt @ parent: " + sectName 
                /*+ "\n\t " +*/, ex/*.getMessage()*/);
      }
    }

    // result is always empty. the update happens at the section manager.
    return factory_.list();
  }

  /**
   * For UnparsedZSect or NarrSect, just return an empty list - no VCs.
   * @param term
   * @return
   */
  @Override
  public List<VC<Pred>> visitSect(Sect term)
  {
    // just ignore other types of Sect
    return factory_.list();
  }

  /**
   * <p>
   * Bootstraps the whole VC generation process by visiting the Z section parents and paragraphs systematically.
   * It takes into account which parents to ignore and the default parents, both of which don't need VC generation.
   * This is also the place where the necessary information tables (per section, namely definition and operator tables)
   * are calculated. This is also the place where the VCG context is created. 
   * </p>
   * <p>
   * The VCG context contains meta-model information extracted from a special Z sect parent: a Z schema with a specific
   * format and shape. This is then used to guide what VCs are needed, depending on the kind of VCG context created.
   * </p>
   */
  @Override
  public List<VC<Pred>> visitZSect(ZSect term)
  {
    List<VC<Pred>> result = factory_.list();
    
    // process section parents, if needed
    result.addAll(collect(term.getParent().toArray(new Parent[term.getParent().size()])));
    
    // calculate necessary tables
    retrieveTables(term);
    
    // creates the VCG context depending on the meta information provided within the Z Sect.
    // if none is available, this might affect some VC generation protocols/algorithms
    // (i.e. feasibility / refinement VCs demand extra context information; DC doesn't).
    retrieveVCGContext(term);
    
    // collect all VCs from the declared paragraphs
    result.addAll(collect(term.getZParaList().toArray(new Para[0])));

    // clear definition and operator tables
    clearNecessaryTables();

    // return collected predicates
    return result;
  }

  /**
   * Method called prior to processing ZSect VCs by {@link #vcsOf(net.sourceforge.czt.z.ast.ZSect)}.
   * Derived classed may want to preprocess information before generating VCs, like loading specific
   * toolkits (e.g., DC loads dc_toolkit).
   * @param zSect
   * @throws VCCollectionException
   */
  protected void beforeGeneratingVCG(ZSect zSect) throws VCCollectionException
  {
    getLogger().finer("VCG-BEFORE-GENERATING-VCS = " + zSect.getName());
  }

  /**
   * Method called after to processing ZSect VCs by {@link #vcsOf(net.sourceforge.czt.z.ast.ZSect)}.
   * Derived classes may want to post process information after generating VCs, as the VC list is also
   * given as a parameters.
   * @param zSect
   * @param vcList list of calculated vcs
   * @throws VCCollectionException
   */
  protected void afterGeneratingVCG(ZSect zSect, List<VC<Pred>> vcList) throws VCCollectionException
  {
    getLogger().finer("VCG-AFTER-GENERATING-VCS = " + zSect.getName());
  }

  /**
   * Creates the VC list for each paragraph within the given ZSect. This method is called by
   * top-level methods creating VCEnvAnn. It starts the visiting of terms for collecting VCs.
   * If processParents is true, all the parents outside {@link #getParentsToIgnore()}
   * are also processed and added to the result.
   * @param zSect ZSect to calculate VCs for
   * @return list of VCs for each paragraph of given Z section
   * @throws VCCollectionException
   */
  //TODO: This method is a good candidate to refactor the VCCollector calculateVC method?
  protected List<VC<Pred>> calculateVCS(ZSect zSect)
          throws VCCollectionException
  {
    // reset VC collector VC count
    getVCCollector().resetVCCount();

    // load the toolkit, if not there already.
    beforeGeneratingVCG(zSect);

    // if we should not process parents, just add ZSect parents to the ignore list
    if (!isProcessingParents())
    {
      for (Parent parent : zSect.getParent())
      {
        addParentSectionToIgnore(parent);
      }
    }

    List<VC<Pred>> result = null;
    try
    {
      // process ZSect for VCs
      result = collect(zSect);
    }
    catch (CztException e)
    {
      Throwable cause = e.getCause();
      if (cause instanceof VCCollectionException)
      {
        throw (VCCollectionException)cause;
      }
      else
        throw new VCCollectionException(getDialect(), "VCG-VCSOF-ZSECT-TERM-VISIT-ERROR", zSect.getName(), cause);
    }
    assert result != null;

    afterGeneratingVCG(zSect, result);

    return result;
  }


  /* VC ZSect CREATION METHODS */

  /**
   * VCSectName suffix. For instance, for domain checking it is "_dc".
   * @param originalSectName original sect name
   * @return new VC Sect name
   */
  // for DC it is just "originalName + _dc"
  public String getVCSectName(String originalSectName) {
    return getVCCollector().getVCNameFactory().getVCSectionName(originalSectName);
  }

  /**
   * Returns the list of parents as a string of section names separated by SectionManager.SECTION_MANAGER_LIST_PROPERTY_SEPARATOR
   * @return
   */
  protected abstract String getVCSectDefaultParentsList();

  protected List<String> splitVCParentsList(String parents)
  {
    return new ArrayList<String>(
      Arrays.asList((parents == null ? "" : parents).split(
       SectionManager.SECTION_MANAGER_LIST_PROPERTY_SEPARATOR)));
    // add at least the original ZSect to it
  }

  /**
   * Creates a list of parents including the given section name, and all
   * those in the {@link #getVCSectDefaultParentsList()} (e.g., if it returns
   * "std_toolkit:mysect" and sectName is "xyz" the list will contain ("xyz", "std_toolkit", "mysect").
   *
   * @param sectName
   * @return
   */
  protected List<? extends Parent> getVCSectParents(String sectName)
  {
    List<Parent> result = factory_.list();
    // get defaults from derived class
    List<String> parentsL = splitVCParentsList(getVCSectDefaultParentsList());
    parentsL.add(sectName);

    // in case of annonymous specs, add standard toolkit
    if (Section.ANONYMOUS.getName().equals(sectName) &&
        !parentsL.contains(Section.STANDARD_TOOLKIT.getName()))
    {
      parentsL.add(0, Section.STANDARD_TOOLKIT.getName());
    }

    for(String s : parentsL)
    {
      result.add(factory_.createParent(s));
    }
    return result;
  }

  /**
   * Creates a ZSect header as "\SECTION sectName_?? \parents sectName, ??" and with empty paragraphs
   * @param sectName
   * @return
   */
  protected ZSect createVCZSectHeader(String sectName)
  {
    ZSect result = factory_.createZSect(
            getVCSectName(sectName),     // foo -> foo_??
            getVCSectParents(sectName),
            factory_.createZParaList());
    return result;
  }

  /**
   * Creates a VCEnvAnn for the given original SectName and given list of VCs.
   * @param vcSectName
   * @param originalSectName
   * @param vcList
   * @return
   */
  // for DC, these two names are trivial and could be just one parameter.
  protected abstract VCEnvAnn newVCEnvAnn(String vcSectName,
          String originalSectName, List<VC<Pred>> vcList);


  /**
   * Creates the ConjPara for the given VC.
   * @param genFormals
   * @param vc
   * @return
   */
  protected abstract ConjPara createVCConjPara(NameList genFormals, VC<Pred> vc);

  /**
   * Default parents for on-the-fly ZSect to generate VC ZSect for.
   * @return list of "standard_toolkit" as parent.
   */
  protected List<? extends Parent> getOnTheFlyZSectParents()
  {
    return factory_.list(factory_.createParent("standard_toolkit"));
  }
  
  protected String createVCZSectPreamble()
  {
    Date date = new Date();
    return "VC ZSection Created at " + date.toString() + ".\n\n";
  }

  protected String createVCZSectPostcript(String sectName, int vcCount, int vcListSize)
  {
    StringBuilder result = new StringBuilder();
    result.append("\n\n VC Z section \"");
    result.append(DefaultVCNameFactory.cleanPossibleNameParameters(sectName));
    result.append("\" has $");
    result.append(vcCount);
    result.append("$");
    result.append(isAddingTrivialVC() ? "" :  " interesting ");
    result.append(vcCount == 1 ? "VC" : "VCs");

    // always add how many trivial ones were hidden, if there are any
    if (/*isAddingTrivialVC() &&*/ vcCount > 0)
    {
      result.append(" (Total = ");
      result.append(vcListSize);
      result.append("; Simplified to $true$ = ");
      result.append(vcListSize - vcCount);
      result.append(")");
    }
    result.append(".\n\n");
    return result.toString();
  }

  private static final String ADDED_PARA_NARR_PARA = "\nAdded schema for feasibility VC signature of paragraph named {0} at {1}.\n";

  /**
   * Adds to the given VC Z section the list of VCs for each
   * corresponding paragraph as a conjecture paragraph. It updates the Z section
   * result list of paragraphs, see {@link #ZSect.getZParaList()}. It also updates
   * the section manager information.
   * @param result Z section to add given list as conjectures.
   * @param vcList list of VCs for each paragraphs to be added to Z section result.
   * @throws VCGException
   */
  public void populateResultsToVCZSect(ZSect result, List<VC<Pred>> vcList)
          throws VCGException
  {
    assert result != null && vcList != null;

    // Add date it was created
    String narrText = createVCZSectPreamble();
    NarrPara narrPara = factory_.createNarrPara(factory_.list(narrText));
    result.getZParaList().add(narrPara);
    boolean addTrivialVC = isAddingTrivialVC();

    // during VCCollection some paras might be added
    for(Para p : getVCCollector().addedPara())
    {
      LocAnn loc = p.getAnn(LocAnn.class);
      Name n = ZUtils.getSchemaName(p);
      final String name;
      if (n != null)
        // take underscores into account
        name = DefaultVCNameFactory.createZNameAsString(ZUtils.assertZName(n));
      else
        name = "unknown";
      narrPara = factory_.createNarrPara(factory_.list(
              MessageFormat.format(ADDED_PARA_NARR_PARA, name, loc != null ? loc.toString() : "unknown")));
      result.getZParaList().add(narrPara);
      result.getZParaList().add(p);
    }

    int vcCount = 0;
    // process each Para DC
    for (VC<Pred> vcI : vcList)
    {
      Para para = vcI.getVCPara();
      
      //!addTrivialDC ==> !(paraDC instanceof TruePred)
      if (addTrivialVC || !vcI.isTrivial())
      {
        
        VCSource sourceInfo = new VCSource(vcI);
        
        // Narrative paragraph with VC information
        narrPara = factory_.createNarrPara(factory_.list(vcI.getInfo()));
        narrPara.getAnns().add(sourceInfo);

        ZNameList genFormals = getGenFormals(para, vcI);
        // create the VC as a conjecture for the VC ZSect
        ConjPara conjPara = createVCConjPara(genFormals, vcI);
        ZName annName = factory_.createZName(vcI.getName());
        conjPara.getAnns().add(annName);
        conjPara.getAnns().add(sourceInfo);
        //conjPara.setName(annName.getWord()); no need here ,since we create the ConjPara without ann

        // add both narrative and dc conjecture paragraphs to the Z section result
        result.getZParaList().add(narrPara);
        result.getZParaList().add(conjPara);
        vcCount++;
      }
    }

    // add narrative para footer with the number of VCs
    narrText = createVCZSectPostcript(result.getName(), vcCount, vcList.size());

    narrPara = factory_.createNarrPara(factory_.list(narrText));
    result.getZParaList().add(narrPara);
  }

  protected ZNameList getGenFormals(Para para, VC<Pred> vc)
  {
    ZNameList genFormals = factory_.createZNameList();
    
    ZNameList vcGenFormals = vc.getGenFormals();
    if (vcGenFormals != null) {
      genFormals.addAll(vcGenFormals);
    } else if (para instanceof AxPara)
    {
   // retrieve genFormals in case of AxPara, or an empty list otherwise
      genFormals.addAll(((AxPara) para).getZNameList());
    }
    else if (para instanceof ConjPara)
    {
      genFormals.addAll(((ConjPara)para).getZNameList());
    }
    return genFormals;
  }

  /* TOP-LEVEL METHODS GENERATING VCS */

  /**
   * VC calculation for the given term, presuming it is a ZSect, Para, Pred,
   * Expr or Decl. The result is Z sections named uniquely with
   * standard toolkits as its parents, and with VC
   * conjectures for the term, if any. The result is a wrapped VCEnvAnn.
   *
   * @param term Z section to generate VCs
   * @param parents list of parents for the on-the-fly section
   * @return VC Z section as a list of VC conjectures
   * @throws VCGException
   */
  public VCEnvAnn createVCEnvAnn(Term term, List<? extends Parent> parents) throws VCGException
  {
    assert term != null : "invalid term for VCG";

    checkSectionManager(term.getClass().getSimpleName());

    Para para;
    if (term instanceof ZSect)
    {
      return createVCEnvAnn((ZSect) term);
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
        zSchText = factory_.createZSchText(factory_.createZDeclList(), (Pred) term);
      }
      else if (term instanceof Expr)
      {
        // [ | pred(Expr) ]
        zSchText = factory_.createZSchText(factory_.createZDeclList(), factory_.createExprPred((Expr) term));
      }
      else if (term instanceof Decl)
      {
        // [ Decl | true ]
        zSchText = factory_.createZSchText(factory_.createZDeclList(factory_.list((Decl) term)), factory_.createTruePred());
      }
      else
      {
        // cannot be processed, raise exception
        throw new VCGException(getDialect(), "VCG-TERM-INVALID = not Para, Decl, Pred, or Expr: " + term.getClass().getName());
      }
      // make it a schema named internally and uniquely
      assert zSchText != null;
      para = factory_.createSchema(factory_.createZName(createUniqueOnTheFlySchemaName()), zSchText);
    }
    assert para != null;

    // create an empty section header: that is, wrap the term as a ZSect inheriting std_toolkit
    ZSect zsect = factory_.createZSect(createUniqueZScectName(), parents, factory_.createZParaList());
    zsect.getZParaList().add(para);

    // add the temporary section to the manager. Do I need the source? No?
    // since these were generated on the fly and do not depend on existing elements in the section manager,
    // just add them without dependencies
    // we don't even need the source, since the ZSect will be in the section manager
//    getManager().put(new Key<Source>(zsect.getName(), Source.class), new StringSource(zsect.toString()));
    getManager().put(new Key<ZSect>(zsect.getName(), ZSect.class), zsect);

    // VC on-the-fly Z section with std_toolkit as parent
    VCEnvAnn result = createVCEnvAnn(zsect);
    return result;
  }

  /**
   * Create VCEnvAnn for term with on-the-fly ZSect with standard toolkit as parent.
   * @param term to calculate VCs for.
   * @return VCs for given term
   * @throws VCGException
   */
  @Override
  public VCEnvAnn createVCEnvAnn(Term term) throws VCGException
  {
    return createVCEnvAnn(term, getOnTheFlyZSectParents());
  }

 
  /**
   * Process the given Z section to generate VCs. The result is a Z sections with the
   * given Z section as its parent, and with generated VCs as conjectures for
   * its paragraphs.
   *
   * @param term Z section to generate VCs
   * @return Z section as a list of VC conjectures
   * @throws VCGException
   */
  @Override
  public VCEnvAnn createVCEnvAnn(ZSect term) throws VCGException
  {
    assert term != null;
    
    // enture the section manager is properly setup.
    final String sectName = term.getName();
    checkSectionManager(sectName);

    // create section header: \SECTION sectName_?? \parents sectName,
    // where ??=DC,AX,PRE,etc for each kind of VC generation
    ZSect zsectVC = createVCZSectHeader(sectName);
    String sectNameVC = zsectVC.getName();
    
    // ensure all parents of zsectVC are parsed - new parents 
    // can be introduced by the VC generator, e.g. function_toolkit
    for (Parent parent : zsectVC.getParent()) {
      try {
        sectManager_.get(new Key<ZSect>(parent.getWord(), ZSect.class));
      }
      catch (CommandException e) {
        throw new VCGException(e.getDialect(), e);
      }
    }
    
    Key<ZSect> vcSectKey = new Key<ZSect>(sectNameVC, ZSect.class);
    sectManager_.startTransaction(vcSectKey);

    List<VC<Pred>> vcList;
    try {
      // get the VCs from term sectName
      vcList = calculateVCS(term);
  
      // update t he VC ZSect and add it to the SectionManager
      // it is accessible as manager.get(new Key<ZSect>(sectName + VCG_GENERAL_NAME_SUFFIX, ZSect.class));
      populateResultsToVCZSect(zsectVC, vcList);
    
    } catch (VCGException e) {
      // exception happened in the middle of transaction - cancel it
      sectManager_.cancelTransaction(vcSectKey);
      // rethrow the exception
      throw e;
    }

    // end the transaction for the generated section - make it explicitly dependent
    // on the source section
    sectManager_.endTransaction(vcSectKey, zsectVC, 
        Collections.singleton(new Key<ZSect>(sectName, ZSect.class)));
    
    // type check generated VC Z section just created
    // on the fly - it ought to succeed
    typeCheck(sectNameVC, false);

    // calculate ThmTable for new VC ZSect
    // why calculate? if someone needs them, will calculate themselves
    // calculateThmTable(sectNameVC);

    // create the result environment - only the original name is needed, but we also given the created name
    VCEnvAnn result = newVCEnvAnn(sectNameVC, sectName, vcList);

    return result;
  }
}
