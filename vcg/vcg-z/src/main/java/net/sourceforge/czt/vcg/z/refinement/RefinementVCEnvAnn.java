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

package net.sourceforge.czt.vcg.z.refinement;

import java.util.List;
import net.sourceforge.czt.base.impl.BaseFactory;
import net.sourceforge.czt.vcg.util.VCNameFactory;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityVCEnvAnn;
import net.sourceforge.czt.z.ast.Pred;

/**
 *
 * @author Leo Freitas
 * @date Aug 31, 2011
 */
public class RefinementVCEnvAnn extends FeasibilityVCEnvAnn implements RefinementPropertyKeys {

  protected RefinementVCEnvAnn(String originalZSectName, List<VC<Pred>> dcs, VCNameFactory vcf)
  {
    super(originalZSectName, dcs, vcf);
  }

  protected RefinementVCEnvAnn(String originalZSectName, List<VC<Pred>> dcs, VCNameFactory vcf,BaseFactory factory)
  {
    super(originalZSectName, dcs, vcf, factory);
  }

  @Override
  public RefinementVCEnvAnn create(Object[] args)
  {
    RefinementVCEnvAnn result = null;
    try
    {
      String originalSectName = (String)args[0];
      @SuppressWarnings("unchecked")
      List<VC<Pred>> dcs = (List<VC<Pred>>)args[1];
      result = new RefinementVCEnvAnn(originalSectName, dcs, getVCNameFactory(), getFactory());
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
  public String getVCSectName()
  {
    return getVCNameFactory().getVCSectionName(getOriginalZSectName());
  }

  /**
   * Compares the specified object with this FactImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) FactImpl and all the getter methods except getAnns
   * return equal objects.
   * @param obj
   * @return
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
   * @return
   */
  @Override
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "RefinementVCEnvAnn".hashCode();
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  @Override
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof RefinementVCEnvAnnVisitor) {
      RefinementVCEnvAnnVisitor<R> visitor = (RefinementVCEnvAnnVisitor<R>) v;
      return visitor.visitRefinementVCEnvAnn(this);
    }
    return super.accept(v);
  }
}