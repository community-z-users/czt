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

import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.vcg.util.DefaultVCNameFactory;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @param <R> 
 * @author Leo Freitas
 * @date Dec 24, 2010
 * $Id$
 */
public abstract class AbstractVC<R> implements VC<R>
{
  private final LocAnn loc_;
  private String name_;
  private final Para para_;
  private final R vc_;
  private final VCType vcType_;
  private final long vcId_;
  private final ZNameList genFormals_;
  
  protected AbstractVC(long vcId, Para term, VCType type, R vc, String name) throws VCCollectionException
  {
    this(vcId, term, type, vc, name, null);
  }
  
  protected AbstractVC(long vcId, Para term, VCType type, R vc, String name, ZNameList genFormals) 
      throws VCCollectionException
  {
    if (term == null || vc == null || type == null || name == null || vcId <= 0)
      throw new VCCollectionException(Dialect.Z, "VC-CTOR-ILLEGAL-ARG-VC");
    vcId_ = vcId;
    para_ = term;
    vcType_ = type;
    vc_ = vc;
    name_ = name;
    genFormals_ = genFormals;
    
    LocAnn paraLoc = para_.getAnn(LocAnn.class);
    if (paraLoc != null)
    {
      // clone the Para loc
      loc_ = (LocAnn)paraLoc.create(paraLoc.getChildren());
      try
      {
        // adjust its factory offset
        ZUtils.assertZPrintVisitor(ZUtils.assertZTermImpl(loc_).getFactory().getToStringVisitor()).setOffset(1, 1);
      }
      catch (UnsupportedAstClassException ast)
      {
        //throw new VCCollectionException("VC-LOCANN-OFFSET-UNAVAILABLE", ast);
        //ignore if not possible.
      } 
      // simplify file name if possible
      if (loc_.getLoc() != null && !loc_.getLoc().isEmpty())
        loc_.setLoc(VCGUtils.getSourceName(loc_.getLoc()));
    }
    else
    {
      loc_ = null;
    }
    
  }

  @Override
  public Para getVCPara()
  {
    return para_;
  }

  @Override
  public VCType getType()
  {
    return vcType_;
  }

  @Override
  public R getVC()
  {
    return vc_;
  }

  @Override
  public long getVCId()
  {
    return vcId_;
  }

  @Override
  public LocAnn getLoc()
  {
    return loc_;
  }

  @Override
  public String getName()
  {
    return name_;
  }
  
  @Override
  public void setVCName(String name)
  {
    name_ = name;
  }

  @Override
  public ZNameList getGenFormals()
  {
    return genFormals_;
  }

  @Override
  public String getInfo()
  {
    // since we cannot retrieve the theorem's name from a latex, neither
    // generate it from a ConjPara, just add some NarrText around instead.
    StringBuilder narrText = new StringBuilder("VC");
    narrText.append(vcId_);
    if (!getType().equals(VCType.NONE))
    {
      narrText.append(" [");
      narrText.append(getType());
      narrText.append("]");
    }
    narrText.append(" for ");
    if (getLoc() != null)
    {
      narrText.append(getLoc().toString());
    }
    else
    {
      narrText.append(getVCPara().toString());
    }
    narrText.append("\n");
    return DefaultVCNameFactory.cleanPossibleNameParameters(narrText.toString());
  }
}
