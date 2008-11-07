/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.z.dc;

import java.util.List;
import java.util.logging.Logger;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
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
      getBooleanProperty(manager, PROP_DOMAINCHECK_USE_INFIX_APPLIESTO);
    boolean processParents =
      getBooleanProperty(manager, PROP_DOMAINCHECK_PROCESS_PARENTS);
    boolean addTrivialDC =
      getBooleanProperty(manager, PROP_DOMAINCHECK_ADD_TRIVIAL_DC);           
    List<String> parentsToIgnore = 
      getListProperty(manager, PROP_DOMAINCHECK_PARENTS_TO_IGNORE);
    
    // reset the domain checker's services and toolkit loading.
    logger_.config("Domain checker command: domain checker confirugation");    
    List<ZSectDCEnvAnn> result = domainCheckUtils_.lDomainCheck(term, manager, 
      parentsToIgnore, useInfixAppliesTo, processParents, addTrivialDC);
    if (result == null || result.size() != 1)
    {
      throw new DomainCheckException("Domain check command returned wrong number of results. Please inspect stack trace. "); 
    }
    return result.get(0);
  }
  
  @Override
  public boolean compute(String name, SectionManager manager) throws CommandException
  { 
    
    //if (!manager.isCached(key)) 
    //{
            
      // parse + typecheck the section - ignore result
      logger_.info("Domain checker command is typechecking " + name);      
      manager.get(new Key<SectTypeEnvAnn>(name, SectTypeEnvAnn.class));       
      
      // retrieve the parsed ZSect
      logger_.info("Domain checker command retrieving typechecked ZSect " + name);      
      ZSect zSect = manager.get(new Key<ZSect>(name, ZSect.class));
      
      logger_.info("Doman checker command is domain checking " + name);
      try
      {
        // calculate domain checks
        logger_.info("Domain checker command is calculating domain checking predicates for " + name);
        List<Pair<Para, Pred>> dcs = domainCheck(zSect, manager);
        
        // update section manager
        logger_.info("Domain checker command is updating section manager information for " + name);
        ZSectDCEnvAnn zsDCEnvAnn = new ZSectDCEnvAnn(zSect, dcs);                      
        manager.put(new Key<ZSectDCEnvAnn>(name, ZSectDCEnvAnn.class), zsDCEnvAnn);      
        return true;
      }
      catch (DomainCheckException e)
      {
        throw new CommandException("Domain check calculation has thrown an exception for Z section " + name, e);
      }          
    //}
  }
  
  protected boolean getBooleanProperty(SectionManager manager,
                                       String propertyKey)
  {
    return "true".equals(manager.getProperty(propertyKey));
  }
  
  protected List<String> getListProperty(SectionManager manager,
                                         String propertyKey)
  {
    return "true".equals(manager.getProperty(propertyKey));
  }
}
