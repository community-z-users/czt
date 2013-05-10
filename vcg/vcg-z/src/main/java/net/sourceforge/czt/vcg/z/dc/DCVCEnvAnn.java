/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.vcg.z.dc;

import java.util.List;
import net.sourceforge.czt.base.impl.BaseFactory;
import net.sourceforge.czt.vcg.util.VCNameFactory;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCEnvAnn;
import net.sourceforge.czt.z.ast.Pred;

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
 * That is because trivial DC (i.e., true) may be omitted according to user's choice.
 * </p>
 * <p>
 * To make it a term within CZT AST, we extend it as an AnnImpl class. In this
 * sense it follows all the CZT protocols for AST terms and their visitation.
 * </p>
 * @author leo
 */
public class DCVCEnvAnn extends VCEnvAnn implements DomainCheckPropertyKeys {
  
  /**
   * Create the given environment as place holder for DC Z sect and its 
   * list of domain checks per paragraph. This list is redundant in the
   * sense that the list encompass all zsect conjectures. The list may contain
   * more paragraph than the Z sect, though. This happens whenever trivial 
   * paragraph have been removed whilst creating the Z section.
   * @param originalZSectName
   * @param dcs
   * @param vcf
   */
  protected DCVCEnvAnn(String originalZSectName, List<VC<Pred>> dcs, VCNameFactory vcf)
  {
    super(originalZSectName, dcs, vcf);
  }
  
  protected DCVCEnvAnn(String originalZSectName, List<VC<Pred>> dcs, VCNameFactory vcf, BaseFactory factory)
  {
    super(originalZSectName, dcs, vcf, factory);
  }
  
  @Override
  public DCVCEnvAnn create(Object[] args)
  {
    DCVCEnvAnn result = null;
    try
    {
      String originalSectName = (String)args[0];      
      @SuppressWarnings("unchecked")
      List<VC<Pred>> dcs = (List<VC<Pred>>)args[1];
      result = new DCVCEnvAnn(originalSectName, dcs, getVCNameFactory(), getFactory());
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
    Object[] erg = { getOriginalZSectName(), getVCs() };
    return erg;
  }

  @Override
  public String getVCSectName()
  {
    return getVCNameFactory().getVCSectionName(getOriginalZSectName());
  }


  /**
   * Compares the specified object with this FactImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) FactImpl and all the getter methods except getAnns
   * return equal objects.
   */
  @Override
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        //DCVCEnvAnn object = (DCVCEnvAnn) obj;// case it
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this FactImpl.
   */
  @Override
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "DCVCEnvAnn".hashCode();
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  @Override
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof DCVCEnvAnnVisitor) {
      DCVCEnvAnnVisitor<R> visitor = (DCVCEnvAnnVisitor<R>) v;
      return visitor.visitDCVCEnvAnn(this);
    }
    return super.accept(v);
  }
}
