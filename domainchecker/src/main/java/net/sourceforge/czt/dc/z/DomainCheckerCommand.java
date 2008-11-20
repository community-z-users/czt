/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.dc.z;

import java.util.List;
import java.util.logging.Logger;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.dc.z.DomainCheckException;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

/**
 *
 * @author leo
 */
public class DomainCheckerCommand 
  implements Command, DomainCheckPropertyKeys {
    
  private static final Logger logger_ = CztLogger.getLogger(DomainChecker.class);
  
  private void typeCheck(ZSect zsect, SectionManager manager) throws CommandException
  {
    // typecheck it        
    logger_.info("Domain checker command is typechecking Z section " + zsect.getName());
    manager.get(new Key<SectTypeEnvAnn>(zsect.getName(), SectTypeEnvAnn.class));
  }  
  
  private ZSectDCEnvAnn retrieveZSectDCEnv(ZSect term, SectionManager manager)
    throws DomainCheckException
  {
    logger_.config("Setting up domain checker command: domain checker confirugation");    
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
    logger_.info("Performing domain check over Z Section " + term.getName());    
    ZSectDCEnvAnn result = DomainCheckUtils.domainCheckUtils_.retrieveZSectDCEnv(term, manager, 
      parentsToIgnore, useInfixAppliesTo, processParents, addTrivialDC, applyPredTransf);
    if (result == null)
    {
      throw new DomainCheckException("Domain check command returned invalid results while" +
        " trying to analyse Z sectin " + term.getName() + ". Please inspect stack trace."); 
    } 
    return result;
  }
  
  private SpecDCEnvAnn retrieveSpecDCEnvAnn(Spec spec, SectionManager manager) 
    throws DomainCheckException
  {
    logger_.config("Setting up domain checker command: domain checker confirugation");    
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
    logger_.info("Performing domain check over Z specification");    
    SpecDCEnvAnn result = DomainCheckUtils.domainCheckUtils_.retrieveSpecDCEnv(spec, manager, 
      parentsToIgnore, useInfixAppliesTo, processParents, addTrivialDC, applyPredTransf);          
    if (result == null)
    {
      throw new DomainCheckException("Domain check command returned invalid results while" +
        " trying to analyse Z specification. Please inspect stack trace."); 
    }
    return result;
  }   
  
  private void addZSectDCEnvAnn(ZSectDCEnvAnn dcs, SectionManager manager)
  {    
    String name = dcs.getOriginalZSectName();
    // update section manager - ADD RESULTS TO THE CACHE
    logger_.info("Domain checker command is updating section manager information for Z section " + name);
    manager.put(new Key<ZSectDCEnvAnn>(name, ZSectDCEnvAnn.class), dcs);                
  }
  
  private void domainCheck(ZSect zsect, SectionManager manager) throws CommandException
  {
    String name = zsect.getName();
    logger_.info("Doman checker command is domain checking Z section " + name);
    try
    {
      // calculate domain checks - results NEED TO BE CACHED
      logger_.info("Domain checker command is calculating domain checking predicates for Z section " + name);
      ZSectDCEnvAnn dcs = retrieveZSectDCEnv(zsect, manager);
      addZSectDCEnvAnn(dcs, manager);
    }
    catch (DomainCheckException e)
    {
      throw new CommandException("Domain check calculation has thrown an exception for Z section " + name, e);
    }
  }
  
  private void domainCheck(String name, Spec spec, SectionManager manager) throws CommandException
  {    
    logger_.info("Doman checker command is domain checking Z specification for " + name);
    try
    {
      // calculate domain checks - results NEED TO BE CACHED
      logger_.info("Domain checker command is calculating domain checking predicates for Z specification for " + name);
      SpecDCEnvAnn dcs = retrieveSpecDCEnvAnn(spec, manager);
      
      // add for all Z Sections the corresponding ZSectDCEnv for each Z Section      
      for(ZSectDCEnvAnn zSectDVEnvAnnd : dcs.getDomainChecks())
      {
        addZSectDCEnvAnn(zSectDVEnvAnnd, manager);
      }      
      
      // update section manager - ADD RESULTS TO THE CACHE
      logger_.info("Domain checker command is updating section manager information for Z specification for " + name);
      manager.put(new Key<SpecDCEnvAnn>(name, SpecDCEnvAnn.class), dcs);            
    }
    catch (DomainCheckException e)
    {
      throw new CommandException("Domain check calculation has thrown an exception for Z specification for " + name, e);
    }
  }
  
  @Override
  public boolean compute(String name, SectionManager manager) throws CommandException
  { 
    // expect name to be a section or specification name. 
    // The result is a SpecDCEnvAnn or ZSectDCEnvAnn.
        
    // parse given term - results are cached 
    logger_.info("Domain checker command parsing Z section (or specification) " + name);          
    Term term = manager.get(new Key<Term>(name, Term.class));
    
    // if name is of cached specification, domain check a spec.
    // if name is of cached Z section, domain check a Z section.         
      
    if (term != null)
    {
      // if name is of a cached Z sect
      if (term instanceof ZSect)
      {
        // type check + domain check it alone
        // this updates the ZSectDCEnvAnn cache for that Z Section
        ZSect zsect = (ZSect)term;
        assert zsect.getName().equals(name);        
        typeCheck(zsect, manager);        
        domainCheck(zsect, manager);
      }  
      // if name is of a cached Z Spec
      else if (term instanceof Spec)
      {  
        // type check + domain check all of its Z Sections
        // this updates the ZSectDCEnvAnn cache for all Z Sections
        // as well as the SpecDCEnvann for the analysed DC Spec
        Spec spec = (Spec)term;
        logger_.info("Domain checker command is typechecking Z specification " + name);
        for(Sect sect : spec.getSect())
        {
          if (sect instanceof ZSect)
          {
            ZSect zsect = (ZSect)sect;
            typeCheck(zsect, manager);            
          }
        }
        domainCheck(name, spec, manager);
      }                             
      return true;
    }
    else
    {
      throw new CommandException("Could not parse while computing domain check command for Z term " + name,
        new DomainCheckException("Domain checking command could not determine nature of Z term " + name));
    }
  }
}
