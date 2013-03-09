/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.vcg.z.feasibility;

import java.util.List;
import net.sourceforge.czt.base.impl.BaseFactory;
import net.sourceforge.czt.vcg.util.VCNameFactory;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCEnvAnn;
import net.sourceforge.czt.z.ast.Pred;

/**
 * <p>
 * Environment containing a Feasibility Z section. It contains a list of
 * feasibility VCs as conjecture paragraphs with conditions
 * for each relevant paragraph of its parent Z section, where these paragraphs
 * come from. One cannot create such terms directly, hence no public constructor.
 * It can only be created through some of the {@link #FeasibilityChecker} methods.
 * </p>
 * @author leo
 */
public class FeasibilityVCEnvAnn extends VCEnvAnn implements FeasibilityPropertyKeys {
  
  protected FeasibilityVCEnvAnn(String originalZSectName, List<VC<Pred>> dcs, VCNameFactory vcf)
  {
    super(originalZSectName, dcs, vcf);
  }
  
  protected FeasibilityVCEnvAnn(String originalZSectName, List<VC<Pred>> dcs, VCNameFactory vcf,BaseFactory factory)
  {
    super(originalZSectName, dcs, vcf, factory);
  }
  
  @Override
  public FeasibilityVCEnvAnn create(Object[] args)
  {
    FeasibilityVCEnvAnn result = null;
    try
    {
      String originalSectName = (String)args[0];      
      @SuppressWarnings("unchecked")
      List<VC<Pred>> dcs = (List<VC<Pred>>)args[1];
      result = new FeasibilityVCEnvAnn(originalSectName, dcs, getVCNameFactory(), getFactory());
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
    hashCode += "FeasibilityVCEnvAnn".hashCode();
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  @Override
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof FeasibilityVCEnvAnnVisitor) {
      FeasibilityVCEnvAnnVisitor<R> visitor = (FeasibilityVCEnvAnnVisitor<R>) v;
      return visitor.visitFeasibilityVCEnvAnn(this);
    }
    return super.accept(v);
  }
}
