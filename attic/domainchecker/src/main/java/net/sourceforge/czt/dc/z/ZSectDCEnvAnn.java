/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.dc.z;

import java.util.Collections;
import java.util.List;
import net.sourceforge.czt.base.impl.BaseFactory;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.impl.AnnImpl;

/**
 * <p>
 * Environment containing a DC Z section. A domain check Z section usually
 * contains a list of conjecture paragraphs with domain checking conditions
 * for each relevant paragraph of its parent Z section, where these paragraphs
 * come from. One cannot create such terms directly, hence no public constructor.
 * It can only be created through some of the {@link #DomainChecker} methods.
 * </p>
 * <p>
 * One can access this information through either the DC Z section
 * itself, or directly through a list of paragraph/predicate pairs. Note that
 * this list may be slightly bigger than the number of conjecture paragraphs.
 * That is because trivial DC (i.e., true) msy be ommitted according to user's choice. 
 * </p>
 * <p>
 * To make it a term within CZT AST, we extend it as an AnnImpl class. In this
 * sense it follows all the CZT protocols for AST terms and their visitation.
 * </p>
 * @author leo
 */
public class ZSectDCEnvAnn extends AnnImpl implements DomainCheckPropertyKeys {

  private String originalZSectName_;
  private List<Pair<Para, Pred>> domainChecks_;
  
  /**
   * Create the given environment as place holder for DC Z sect and its 
   * list of domain checks per paragraph. This list is redundant in the
   * sense that the list encompass all zsect conjectures. The list may contain
   * more paragraph than the Z sect, though. This happens whenever trivial 
   * paragraph have been removed whilst creating the Z section.
   * @param originalZSectName
   * @param dcs
   */
  protected ZSectDCEnvAnn(String originalZSectName, List<Pair<Para, Pred>> dcs)
  {
    super();
    init(originalZSectName, dcs);
  }
  
  protected ZSectDCEnvAnn(String originalZSectName, List<Pair<Para, Pred>> dcs, BaseFactory factory)    
  {
    super(factory);
    init(originalZSectName, dcs);
  }
  
  protected final void init(String originalZSectName, List<Pair<Para, Pred>> dcs)
  {
    assert dcs != null : "null list of domain checks";
    assert originalZSectName != null && !originalZSectName.isEmpty() : "invalid Z section name";
    originalZSectName_ = originalZSectName;
    domainChecks_ = Collections.unmodifiableList(dcs);
  }

  /**
   * Compares the specified object with this ZNameImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) ZNameImpl and all the getter methods except getAnns
   * return equal objects.
   * @param obj
   */
  @Override
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        ZSectDCEnvAnn object = (ZSectDCEnvAnn) obj;
        if (originalZSectName_ != null) {
          if (!originalZSectName_.equals(object.originalZSectName_)) {
            return false;
          }
        }
        else {
          if (object.originalZSectName_ != null) {
            return false;
          }
        }        
        if (domainChecks_ != null) {
          if (!domainChecks_.equals(object.domainChecks_)) {
            return false;
          }
        }
        else {
          if (object.domainChecks_ != null) {
            return false;
          }
        }        
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this ZNameImpl.
   */
  @Override
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "ZSectDCEnvAnn".hashCode();
    if (originalZSectName_ != null) {
      hashCode += constant * originalZSectName_.hashCode();
    }    
    if (domainChecks_ != null) {
      hashCode += constant * domainChecks_.hashCode();
    }    
    return hashCode;
  }

  /**
   * Accepts a visitor.
   * @param <R> 
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof ZSectDCEnvAnnVisitor) {
      ZSectDCEnvAnnVisitor<R> visitor = (ZSectDCEnvAnnVisitor<R>) v;
      return visitor.visitZSectDCEnvAnn(this);
    }     
    return super.accept(v);
  }
  
  public ZSectDCEnvAnn create(Object[] args)
  {
    ZSectDCEnvAnn result = null;
    try
    {
      String originalSectName = (String)args[0];      
      @SuppressWarnings("unchecked")
      List<Pair<Para, Pred>> dcs = (List<Pair<Para, Pred>>)args[1];
      result = new ZSectDCEnvAnn(originalSectName, dcs, getFactory());
    }
    catch (IndexOutOfBoundsException e) 
    {
      throw new IllegalArgumentException(e);
    }
    catch (ClassCastException e) 
    {
      throw new IllegalArgumentException(e);
    }
    return result;    
  }

  @Override
  public Object[] getChildren()
  {
    Object[] erg = { getOriginalZSectName(), getDomainChecks() };
    return erg;
  }
  
  public String getOriginalZSectName()
  {
    return originalZSectName_;
  }

  public String getDCZSectName()
  {
    return originalZSectName_ + DOMAIN_CHECK_GENERAL_NAME_SUFFIX;
  }
  
  public List<Pair<Para, Pred>> getDomainChecks()
  {
    return domainChecks_;
  }
}
