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
import net.sourceforge.czt.z.impl.AnnImpl;

/**
 *
 * @param <R>
 * @author Leo Freitas
 * @date Dec 23, 2010
 */
public abstract class VCEnvAnn<R> extends AnnImpl implements VCGPropertyKeys
{
  private String originalZSectName_;
  private List<VC<R>> vcs_;
  
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
   */
  protected VCEnvAnn(String originalZSectName, List<VC<R>> vcs)
  {
    super();
    init(originalZSectName, vcs);
  }

  protected VCEnvAnn(String originalZSectName, List<VC<R>> vcs, BaseFactory factory)
  {
    super(factory);
    init(originalZSectName, vcs);
  }

  protected final void init(String originalZSectName, List<VC<R>> vcs)
  {
    assert vcs != null : "null list of vcs";
    assert originalZSectName != null && !originalZSectName.isEmpty() : "invalid Z section name";
    originalZSectName_ = originalZSectName;
    vcs_ = Collections.unmodifiableList(vcs);
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
      return visitor.visitVCGEnvAnn((VCEnvAnn<R>) this);
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

  public List<VC<R>> getVCs()
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
