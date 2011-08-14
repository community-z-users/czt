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
import net.sourceforge.czt.z.ast.Spec;
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
public class SpecDCEnvAnn extends AnnImpl implements DomainCheckPropertyKeys {

  /**
   * String pointing to the Source key name for the original
   * specification. That is, one shoulud be able to retrieve 
   * from the section manager to get two Spec terms using 
   * this name as:
   * 
   * <ul>
   *   <li><code>originalSpec = manager.get(new Key&lt;Spec&gt;(originalSpecResourceName_, Spec.class))</code></li>
   *   <li><code>dcSpec =manager.get(new Key&lt;Spec&gt;(originalSpecResourceName_ + DOMAIN_CHECK_GENERAL_NAME_SUFFIX, Spec.class))</code></li>
   * </ul>
   */
  private String originalSpecResourceName_;
  private List<ZSectDCEnvAnn> domainChecks_;
  
  protected SpecDCEnvAnn(List<ZSectDCEnvAnn> dcs)
  {
    this("Specification", dcs);
  }
  
  /**
   * Create the given environment as place holder for DC Z sect and its 
   * list of domain checks per paragraph. This list is redundant in the
   * sense that the list encompass all zsect conjectures. The list may contain
   * more paragraph than the Z sect, though. This happens whenever trivial 
   * paragraph have been removed whilst creating the Z section.
   * @param zsect
   * @param dcs
   */
  protected SpecDCEnvAnn(String originalSpecResName, List<ZSectDCEnvAnn> dcs)
  {
    super();
    init(originalSpecResName, dcs);
  }
  
  protected SpecDCEnvAnn(String originalSpecResName,  List<ZSectDCEnvAnn> dcs, BaseFactory factory)    
  {
    super(factory);
    init(originalSpecResName, dcs);
  }
  
  protected void init(String originalSpecResName, List<ZSectDCEnvAnn> dcs)
  {
    assert dcs != null : "null list of domain checks";
    assert originalSpecResName != null : "null specification resource name";
    originalSpecResourceName_ = originalSpecResName;    
    domainChecks_ = Collections.unmodifiableList(dcs);
  }

  /**
   * Compares the specified object with this ZNameImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) ZNameImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        SpecDCEnvAnn object = (SpecDCEnvAnn) obj;
        if (originalSpecResourceName_ != null) {
          if (!originalSpecResourceName_.equals(object.originalSpecResourceName_)) {
            return false;
          }
        }
        else {
          if (object.originalSpecResourceName_ != null) {
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
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "ZSpecDCEnvAnn".hashCode();
    if (originalSpecResourceName_ != null) {
      hashCode += constant * originalSpecResourceName_.hashCode();
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
    if (v instanceof SpecDCEnvAnnVisitor) {
      SpecDCEnvAnnVisitor<R> visitor = (SpecDCEnvAnnVisitor<R>) v;
      return visitor.visitZSpecDCEnvAnn(this);
    }     
    return super.accept(v);
  }
  
  public SpecDCEnvAnn create(Object[] args)
  {
    SpecDCEnvAnn result = null;
    try
    {
      String originalResName = (String)args[0];      
      @SuppressWarnings("unchecked")
      List<ZSectDCEnvAnn> dcs = (List<ZSectDCEnvAnn>)args[1];
      result = new SpecDCEnvAnn(originalResName, dcs, getFactory());
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
    Object[] erg = { getOriginalSpecResourceName(), getDomainChecks() };
    return erg;
  }
  
  public String getOriginalSpecResourceName()
  {
    return originalSpecResourceName_;
  }  
  
  public List<ZSectDCEnvAnn> getDomainChecks()
  {
    return domainChecks_;
  }
  
  // convenience methods
  public Spec getDCSpec(SectionInfo manager) throws DomainCheckException
  {    
    assert manager != null : "invalid section manager";
    try
    {
      System.out.println("Retrieving SpecDCEnvAnn.DCSpec for " + getOriginalSpecResourceName() + DOMAIN_CHECK_GENERAL_NAME_SUFFIX);
      return manager.get(new Key<Spec>(getOriginalSpecResourceName() + DOMAIN_CHECK_GENERAL_NAME_SUFFIX, Spec.class));
    }
    catch (CommandException ex)
    {
      throw new DomainCheckException("Could not retrieve domain checked ZSect " + getOriginalSpecResourceName() +
        ". That is a severe error and should never happen when SpecDCEnvAnn is created properly.");
    }    
  }
}
