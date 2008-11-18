/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.dc.z;

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztLogger;
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
  
  private static final DomainCheckUtils domainCheckUtils_ = new DomainCheckUtils();
  private static final Logger logger_ = CztLogger.getLogger(DomainChecker.class);
      
  protected ZSectDCEnvAnn domainCheck(ZSect term, SectionManager manager)
    throws DomainCheckException
  {
    boolean useInfixAppliesTo =
      (manager.hasProperty(PROP_DOMAINCHECK_USE_INFIX_APPLIESTO) ?
        manager.getBooleanProperty(PROP_DOMAINCHECK_USE_INFIX_APPLIESTO) :
        DCTerm.APPLIESTO_INFIX_DEFAULT);
    boolean processParents =
      (manager.hasProperty(PROP_DOMAINCHECK_PROCESS_PARENTS) ?
        manager.getBooleanProperty(PROP_DOMAINCHECK_PROCESS_PARENTS) :
        DomainChecker.DEFAULT_PROCESS_PARENTS);
    boolean addTrivialDC =
      (manager.hasProperty(PROP_DOMAINCHECK_ADD_TRIVIAL_DC) ?
        manager.getBooleanProperty(PROP_DOMAINCHECK_ADD_TRIVIAL_DC) :
        DomainChecker.DEFAULT_ADD_TRIVIAL_DC);
    boolean applyPredTransf =
      (manager.hasProperty(PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS) ?
        manager.getBooleanProperty(PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS) :
        DCTerm.APPLY_PRED_TRANSFORMERS_DEFAULT);
    List<String> parentsToIgnore = 
      (manager.hasProperty(PROP_DOMAINCHECK_PARENTS_TO_IGNORE) ? 
       manager.getListProperty(PROP_DOMAINCHECK_PARENTS_TO_IGNORE) : null);
    
    // reset the domain checker's services and toolkit loading.
    logger_.config("Domain checker command: domain checker confirugation");    
    ZSectDCEnvAnn result = domainCheckUtils_.retrieveZSectDCEnv(term, manager, 
      parentsToIgnore, useInfixAppliesTo, processParents, addTrivialDC, applyPredTransf);
    if (result == null)
    {
      throw new DomainCheckException("Domain check command returned invalid results. Please inspect stack trace."); 
    }
    return result;
  }
  
  @Override
  public boolean compute(String name, SectionManager manager) throws CommandException
  { 
    // expect name to be a section name. The result is a singler ZSectEnvAnn, so, it must be a ZSect.
    
    //if (!manager.isCached(key)) 
    //{            
      // parse given term - results are cached 
      logger_.info("Domain checker command parsing Z section" + name);      
      ZSect zsect = manager.get(new Key<ZSect>(name, ZSect.class));
      
      if (zsect != null)
      {
        assert zsect.getName().equals(name);
        // typecheck it        
        logger_.info("Domain checker command is typechecking Z section " + name);
        manager.get(new Key<SectTypeEnvAnn>(name, SectTypeEnvAnn.class));
      }
      else
      {
        throw new CommandException("Could not parse while computing domain check command for Z section " + name,
          new DomainCheckException("Domain checking command could not determine nature of Z section " + name));
      }
        
      logger_.info("Doman checker command is domain checking Z section" +name);
      try
      {
        // calculate domain checks - results NEED TO BE CACHED
        logger_.info("Domain checker command is calculating domain checking predicates for Z section " + name);
        ZSectDCEnvAnn dcs = domainCheck(zsect, manager);

        // update section manager - ADD RESULTS TO THE CACHE
        logger_.info("Domain checker command is updating section manager information for Z section " + name);
        manager.put(new Key<ZSectDCEnvAnn>(dcs.getZSect().getName(), ZSectDCEnvAnn.class), dcs);                
      }
      catch (DomainCheckException e)
      {
        throw new CommandException("Domain check calculation has thrown an exception for Z section " + name, e);
      }               
    //}
    return true;
  }
}
