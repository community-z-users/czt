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
package net.sourceforge.czt.vcg.z.dc;

import java.util.List;
import java.util.SortedSet;

import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.z.AbstractVCG;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCCollector;
import net.sourceforge.czt.vcg.z.VCEnvAnn;
import net.sourceforge.czt.vcg.z.VCGException;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.NameList;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZUtils;

/**
 * <p>
 * Top-level domain checking class. Given a Z section or specification, it 
 * calculates the list of conjectures for each relevant paragraph. The results
 * are delivered either as child Z section with a list of conjectures or as a
 * list of paragraph / predicate pairs. For details on the nature of domain 
 * checks and their shape for every Z term, see {@link #DCVCCollector}.
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
public class DomainCheckerVCG extends 
			AbstractVCG<Type2, SortedSet<Definition>> //<Pred> //AbstractTermVCG<List<Pair<Para, Pred>>>
        implements DomainCheckPropertyKeys
{

  private ZSect dcToolkit_;
  private final DCVCCollector domainCheck_;
  
  /* CLASS SETUP METHOS */

  public DomainCheckerVCG()
  {
    this(ZUtils.createConsoleFactory());
  }

  public DomainCheckerVCG(Factory factory)
  {
    super(factory);
    domainCheck_ = new DCVCCollector(factory);
  }

  @Override
  protected boolean defaultAddTrivialVC()
  {
    return PROP_VCG_DOMAINCHECK_ADD_TRIVIAL_VC_DEFAULT;
  }

  @Override
  protected boolean defaultRaiseTypeWarnings()
  {
    return PROP_VCG_DOMAINCHECK_RAISE_TYPE_WARNINGS_DEFAULT;
  }

  @Override
  protected boolean defaultProcessParents()
  {
    return PROP_VCG_DOMAINCHECK_PROCESS_PARENTS_DEFAULT;
  }

  @Override
  protected boolean defaultApplyTransformers()
  {
    return PROP_VCG_DOMAINCHECK_APPLY_TRANSFORMERS_DEFAULT;
  }

  @Override
  protected SortedSet<String> defaultParentsToIgnore()
  {
    SortedSet<String> result = super.defaultParentsToIgnore();
    result.add(VCG_DOMAINCHECK_TOOLKIT_NAME);
    return result;
  }

  protected boolean defaultInfixAppliesTo()
  {
    return PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO_DEFAULT;
  }

  @Override
  public VCCollector<//Pred,
  					 Type2, SortedSet<Definition>> getVCCollector()
  {
    return domainCheck_;
  }

  /**
   * 
   * @return
   */
  public boolean isUsingInfixAppliesTo()
  {
    return domainCheck_.isAppliesToInfix();
  }

  /**
   * 
   * @param value
   */
  public void setInfixAppliesTo(boolean value)
  {
    domainCheck_.setInfixAppliesTo(value);
  }


  /* VCG CONFIGURATION METHODS */

  @Override
  public void reset()
  {
    setInfixAppliesTo(defaultInfixAppliesTo());
    super.reset();
  }

  @Override
  protected void doConfig() throws VCGException
  {
    super.doConfig();
    SectionManager manager = getManager();
    boolean appliesTo = getManager().hasProperty(PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO) ?
          manager.getBooleanProperty(PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO) : defaultInfixAppliesTo();

    setInfixAppliesTo(appliesTo);
  }

  @Override
  protected void doDefaultProperties(SectionManager manager)
  {
    super.doDefaultProperties(manager);
    manager.setProperty(PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO, String.valueOf(defaultInfixAppliesTo()));
  }

  /* VC CALCULATION TERM VISITING METHODS */

  /**
   * Method called prior to processing ZSect VCs by {@link #vcsOf(net.sourceforge.czt.z.ast.ZSect)}.
   * Derived classed may want to preprocess information before generating VCs, like loading specific
   * toolkits (e.g., DC loads dc_toolkit).
   * @param zSect
   * @throws VCCollectionException
   */
  @Override
  protected void beforeGeneratingVCG(ZSect zSect) throws VCCollectionException
  {
    super.beforeGeneratingVCG(zSect);
    loadDCToolkit();
  }

  @Override
  protected boolean isTableMandatory(Key<? extends InfoTable> key)
  {
    return false; // for DC, no tables are mandatory
  }

  @Override
  protected boolean shouldTryTableAgain(Key<? extends InfoTable> key)
  {
    return false; // for DC, never try again, whatever the table
  }


  /**
   * Method called after to processing ZSect VCs by {@link #vcsOf(net.sourceforge.czt.z.ast.ZSect)}.
   * Derived classes may want to post process information after generating VCs, as the VC list is also
   * given as a parameters.
   * @param zSect
   * @param vcList list of calculated vc
   * @throws VCCollectionException
   */
  @Override
  protected void afterGeneratingVCG(ZSect zSect, List<VC<Pred>> vcList) throws VCCollectionException
  {
    // TODO: anything to do here?
    super.afterGeneratingVCG(zSect, vcList);
  }

  /**
   * Loads the Domain check toolkit containing necessary definitions for the DC VCs.
   * 
   * @throws VCCollectionException
   */
  private void loadDCToolkit() throws VCCollectionException
  {
    assert isConfigured() : "Cannot load " + VCG_DOMAINCHECK_TOOLKIT_NAME + " without a section manager!";
    if (dcToolkit_ == null)
    {
      // parse and typecheck the dcToolkit within the section manager so that that operator
      // table for (_ appliesTo _) is available within it.
      SectTypeEnvAnn type = null;
      SectionManager manager = getManager();
      try
      {
        dcToolkit_ = manager.get(new Key<ZSect>(VCG_DOMAINCHECK_TOOLKIT_NAME, ZSect.class));
        type = manager.get(new Key<SectTypeEnvAnn>(VCG_DOMAINCHECK_TOOLKIT_NAME, SectTypeEnvAnn.class));
      }
      catch (CommandException e)
      {
        if (dcToolkit_ == null) 
        {
			throw new DomainCheckException(getDialect(), "VCG-DC-TOOLKIT-PARSE-ERROR", e);
		} 
        else if (type == null) 
		{
			throw new DomainCheckException(getDialect(), "VCG-DC-TOOLKIT-TYPE-ERROR", e);
		} 
        // TODO: why is this dead code?
        //else throw new DomainCheckException("VCG-DC-TOOLKIT-CMD-ERROR", e);
      }
      assert type != null : "Could not typecheck DC toolkit";
      assert dcToolkit_ != null : "Could not load DC toolkit";
    }
  }

  /* VC ZSect CREATION METHODS */

  @Override
  public Class<? extends VCEnvAnn> getVCEnvAnnClass()
  {
    return DCVCEnvAnn.class;
  }

  /**
   * List of default parents for VC ZSect. For Domain check this is just "dc_toolkit".
   *
   * @return
   */
  @Override
  protected String getVCSectDefaultParentsList()
  {
    // if more than one, separate with SectionManager.SECTION_MANAGER_LIST_PROPERTY_SEPARATOR
    return VCG_DOMAINCHECK_TOOLKIT_NAME;
  }

  @Override
  protected VCEnvAnn newVCEnvAnn(String vcSectName, String originalSectName, List<VC<Pred>> vcList)
  {
    // Or get the getVCCollector().getVCNameFactory()?
    return new DCVCEnvAnn(originalSectName, vcList, getVCCollector().getVCNameFactory());
  }

  @Override
  protected ConjPara createVCConjPara(NameList genFormals, VC<Pred> vc)
  {
    return getFactory().createConjPara(genFormals, vc.getVC());
  }

  @Override
  protected String createVCZSectPreamble()
  {
    String result = "\\newcommand{\\appliesTo}{\\zbinop{appliesTo}} \n\\newcommand{\\appliesToNofix}{\\zpreop{appliesToNofix}} \n\n";
    result += super.createVCZSectPreamble();
    return result;
  }
}
