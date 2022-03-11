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

package net.sourceforge.czt.vcg.z;

import java.util.Collections;
import java.util.List;
import net.sourceforge.czt.base.impl.BaseFactory;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.vcg.util.VCNameFactory;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.impl.AnnImpl;

/**
 *
 * @author Leo Freitas
 * @date Dec 23, 2010
 */
// NOTE: I removed the R type parameter since VCs are always a Pred (so far) anyway.
//		 And even if they were to be something different, that would be strange. 
//		 Go back to the generic version if needed. This was on "zvcg" branch on 9/3/2013
//		 Sha1 @ git-rep = bad8c4d858ffaea2c4606aa7c0cf67e3b0a2b673
public abstract class VCEnvAnn extends AnnImpl implements VCGPropertyKeys
{
  private VCNameFactory vcNameFactory_;
  private String originalZSectName_;
  private List<VC<Pred>> vcs_;
  
  /**
   * Create the given environment as place holder a VC ZSect list of VCs per paragraph.
   * This list is redundant in the sense that the list encompass all ZSect conjectures.
   * The list may contain more paragraphs than the Z sect. This happens whenever there
   * are more than one VC per paragraph, or even the less VCs than paragraph whenever
   * trivial paragraph VCs have been removed whilst creating the Z section.
   * This class is like the ThmTable class.
   *
   * @param originalZSectName ZSect where the VCs came from
   * @param vcs list of VC per paragraph.
   * @param vcf
   */
  protected VCEnvAnn(String originalZSectName, List<VC<Pred>> vcs, VCNameFactory vcf)
  {
    super();
    init(originalZSectName, vcs, vcf);
  }

  protected VCEnvAnn(String originalZSectName, List<VC<Pred>> vcs, VCNameFactory vcf, BaseFactory factory)
  {
    super(factory);
    init(originalZSectName, vcs, vcf);
  }

  protected final void init(String originalZSectName, List<VC<Pred>> vcs, VCNameFactory vcf)
  {
    assert vcs != null : "null list of vcs" ;
    assert vcf != null : "vc name factory is null";
    assert originalZSectName != null && !originalZSectName.isEmpty() : "invalid Z section name";
    originalZSectName_ = originalZSectName;
    vcNameFactory_ = vcf;
    vcs_ = Collections.unmodifiableList(vcs);
  }

  protected VCNameFactory getVCNameFactory()
  {
    return vcNameFactory_;
  }

  /**
   * Accepts a visitor.
   * @param <R>
   * @param v
   */
  @Override
  public <R> R accept(Visitor<R> v)
  {
    if (v instanceof VCEnvAnnVisitor)
    {
      VCEnvAnnVisitor<R> visitor = (VCEnvAnnVisitor<R>) v;
      return visitor.visitVCGEnvAnn(this);
    }
    return super.accept(v);
  }

  /**
   * Compares the specified object with this ZNameImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) ZNameImpl and all the getter methods except getAnns
   * return equal objects.
   * @param obj
   * @return
   */
  @Override
  public boolean equals(Object obj)
  {
    if (obj != null)
    {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj))
      {
        VCEnvAnn object = (VCEnvAnn) obj;
        if (originalZSectName_ != null)
        {
          if (!originalZSectName_.equals(object.originalZSectName_))
          {
            return false;
          }
        }
        else
        {
          if (object.originalZSectName_ != null)
          {
            return false;
          }
        }
        if (vcs_ != null)
        {
          if (!vcs_.equals(object.vcs_))
          {
            return false;
          }
        }
        else
        {
          if (object.vcs_ != null)
          {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  public abstract String getVCSectName();

  public List<VC<Pred>> getVCs()
  {
    return Collections.unmodifiableList(vcs_);
  }

  public String getOriginalZSectName()
  {
    return originalZSectName_;
  }

  /**
   * Returns the hash code value for this ZNameImpl.
   * @return
   */
  @Override
  public int hashCode()
  {
    final int constant = 31;
    int hashCode = super.hashCode();
    hashCode += "VCEnvAnn".hashCode();
    if (originalZSectName_ != null)
    {
      hashCode += constant * originalZSectName_.hashCode();
    }
    if (vcs_ != null)
    {
      hashCode += constant * vcs_.hashCode();
    }
    return hashCode;
  }
}
