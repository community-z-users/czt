/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.dc.z;

import net.sourceforge.czt.session.AbstractCommand;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.util.SectTypeEnv;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.ZSect;

/**
 *
 * @author leo
 */
public class DomainCheckerCommand extends AbstractCommand
        implements DomainCheckPropertyKeys {

  private ZSect parse(String name, SectionManager manager) throws CommandException
  {
    traceLog("DC-parse = " + name);
    // parse given term - results are cached
    //Term term = manager.get(new Key<Term>(name, Term.class));
    ZSect zSect = manager.get(new Key<ZSect>(name, ZSect.class));
    return zSect;
  }
  /**
   * Type check given ZSect. Throws a CommandException in case of type errors
   *
   * @param zsect
   * @param manager
   * @return type environment for ZSect
   * @throws CommandException
   */
  private SectTypeEnvAnn typeCheck(String name, SectionManager manager) throws CommandException
  {
    // typecheck ZSect
    traceLog("DC-typeck = " + name);
    SectTypeEnvAnn result = manager.get(new Key<SectTypeEnvAnn>(name, SectTypeEnvAnn.class));
    return result;
  }

  /**
   *
   * @param zsect
   * @param manager
   * @throws CommandException
   */
  private void domainCheck(ZSect zSect, SectionManager manager) throws CommandException
  {
    // config the domain checker according to the given section manager 
    traceLog("DCCmd-ZSECT-CONFIG");
    DomainCheckUtils.getDCUtils().getDC().setSectInfo(manager);

    // compute ZSectDCEnvAnn for a given ZSect:
    //    a) assume zSect is: parsed, type correct, and with all SM tables in place
    //    b) create ZSect term; adds DefTable, OpTable, etc to SM
    traceLog("DC-ZSECT-COMPUTE = " + zSect.getName());
    ZSectDCEnvAnn result = DomainCheckUtils.getDCUtils().calculateZSectDCEnv(zSect);

    // type check resulting DC ZSection
    //    c) adds SectTypeEnv to SM
    typeCheck(result.getDCZSectName(), manager);

    // update section manager with ZSectDCEnvAnn
    //    d) adds ZSectDCEnvAnn to SM
    assert result != null : "Should throw DomainCheckException when fail";
    manager.put(new Key<ZSectDCEnvAnn>(result.getOriginalZSectName(), ZSectDCEnvAnn.class), result);
  }
  

  /* TODO: remove this? Like TypeCheckCommand, just process ZSect and let top-level app handle Spec?
  private SpecDCEnvAnn retrieveSpecDCEnvAnn(Spec spec, SectionManager manager) 
    throws DomainCheckException
  {
    traceLog("DC-SPEC-CONFIG");
    boolean useInfixAppliesTo =
      (manager.hasProperty(PROP_DOMAINCHECK_USE_INFIX_APPLIESTO) ?
        manager.getBooleanProperty(PROP_DOMAINCHECK_USE_INFIX_APPLIESTO) :
        PROP_DOMAINCHECK_USE_INFIX_APPLIESTO_DEFAULT);
    boolean processParents =
      (manager.hasProperty(PROP_DOMAINCHECK_PROCESS_PARENTS) ?
        manager.getBooleanProperty(PROP_DOMAINCHECK_PROCESS_PARENTS) :
        PROP_DOMAINCHECK_PROCESS_PARENTS_DEFAULT);
    boolean addTrivialDC =
      (manager.hasProperty(PROP_DOMAINCHECK_ADD_TRIVIAL_DC) ?
        manager.getBooleanProperty(PROP_DOMAINCHECK_ADD_TRIVIAL_DC) :
        PROP_DOMAINCHECK_ADD_TRIVIAL_DC_DEFAULT);
    boolean applyPredTransf =
      (manager.hasProperty(PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS) ?
        manager.getBooleanProperty(PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS) :
        PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS_DEFAULT);
    List<String> parentsToIgnore = 
      (manager.hasProperty(PROP_DOMAINCHECK_PARENTS_TO_IGNORE) ? 
       manager.getListProperty(PROP_DOMAINCHECK_PARENTS_TO_IGNORE) : null);
    
    // reset the domain checker's services and toolkit loading.    
    traceLog("DC-SPEC-COMPUTE");
    SpecDCEnvAnn result = DomainCheckUtils.domainCheckUtils_.calculateSpecDCEnv(spec, manager,
      parentsToIgnore, useInfixAppliesTo, processParents, addTrivialDC, applyPredTransf);          
    if (result == null)
    {
      throw new DomainCheckException("Domain check command returned invalid results while" +
        " trying to analyse Z specification. Please inspect stack trace."); 
    }
    return result;
  }

   private void domainCheck(String name, Spec spec, SectionManager manager) throws CommandException
  {    
    try
    {
      // calculate domain checks - results NEED TO BE CACHED
      SpecDCEnvAnn dcs = retrieveSpecDCEnvAnn(spec, manager);
      
      // add for all Z Sections the corresponding ZSectDCEnv for each Z Section      
      for(ZSectDCEnvAnn zSectDVEnvAnnd : dcs.getDomainChecks())
      {
        addZSectDCEnvAnn(zSectDVEnvAnnd, manager);
      }      
      
      // update section manager - ADD RESULTS TO THE CACHE
      manager.put(new Key<SpecDCEnvAnn>(name, SpecDCEnvAnn.class), dcs);            
    }
    catch (DomainCheckException e)
    {
      throw new CommandException("Domain check calculation has thrown an exception for Z specification for " + name, e);
    }
  }
  */

  /**
   * To compute domain checks we need the specification or section name.
   * It uses TermCommand to retrieve/parse the Specification/ZSection.
   * It is then type checked, and only if no problems arise, domain checked.
   * That is, we assume the resource to be well formed before we perform domain checks.
   *
   * @param name
   * @return
   * @throws CommandException
   */
  @Override
  public boolean compute(String name, SectionManager manager) throws CommandException
  { 
    // expect name to be a section or specification name. 
    // The result is a SpecDCEnvAnn or ZSectDCEnvAnn.

    ZSect zSect = parse(name, manager);

    // if name is of cached specification, domain check a spec.
    // if name is of cached Z section, domain check a Z section.         
    //if (zSect != null)
    //{
      // if name is of a cached Z sect
      //if (term instanceof ZSect)
      //{
        // type check + domain check it alone
        // this updates the ZSectDCEnvAnn cache for that Z Section
        //ZSect zSect = (ZSect)term;
        //assert zSect.getName().equals(name);
        typeCheck(name, manager);
        domainCheck(zSect, manager);
      //}
      // if name is of a cached Z Spec
      //else if (term instanceof Spec)
      //{  
      //  // type check + domain check all of its Z Sections
      //  // this updates the ZSectDCEnvAnn cache for all Z Sections
      //  // as well as the SpecDCEnvann for the analysed DC Spec
      //  Spec spec = (Spec)term;
      // for(Sect sect : spec.getSect())
      //  {
      //    if (sect instanceof ZSect)
      //    {
      //      ZSect zsect = (ZSect)sect;
      //      typeCheck(zsect, manager);
      //    }
      //  }
      //  domainCheck(name, spec, manager);
      //}
      return true;
    //}
    //else
    //{
    //  throw new CommandException("Could not parse while computing domain check command for Z term " + name,
    //    new DomainCheckException("Domain checking command could not determine nature of Z term " + name));
    //}
  }
}
