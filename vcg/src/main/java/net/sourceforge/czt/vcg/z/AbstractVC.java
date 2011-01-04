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
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @param <R> 
 * @author Leo Freitas
 * @date Dec 24, 2010
 */
public abstract class AbstractVC<R> implements VC<R>
{
  private final LocAnn loc_;
  private String name_;
  private final Para para_;
  private final R vc_;
  private final VCType vcType_;
  
  private static long axiomCnt_ = 0;
  private static long vcCnt_ = 0;

  protected AbstractVC(Para term, VCType type, R vc) throws VCCollectionException
  {
    if (term == null || vc == null || type == null)
      throw new VCCollectionException("VC-CTOR-NULL-TERMVC");
    para_ = term;
    vcType_ = type;
    vc_ = vc;
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
    }
    else
    {
      loc_ = null;
    }

    // create a candidate VC name
    name_ = createVCName(term);
  }

  /**
   * For any given Z Paragraph, extract a meaningful name for this VC. It also
   * counts how many axioms there are.
   * @param para
   * @return
   */
  protected final String createVCName(Para para)
  {
    // create the conjecture name or internal axiom name
    String conjName = null;
    ZName conjPrefix = null;
    if (ZUtils.isAbbreviation(para))
    {
      conjPrefix = ZUtils.assertZName(ZUtils.getAbbreviationName(para));
    }
    else if (ZUtils.isSimpleSchema(para))
    {
      conjPrefix =ZUtils.assertZName(ZUtils.getSchemaName(para));
    }
    else if (para instanceof ConjPara)
    {
      conjName = ((ConjPara) para).getName();
    }
    else if (para instanceof FreePara)
    {
      // for multiple free types, just get the first name available.
      conjPrefix = ZUtils.assertZFreetypeList(((FreePara) para).getFreetypeList()).get(0).getZName();
    }
    else if (ZUtils.isAxPara(para) && ((AxPara) para).getBox().equals(Box.AxBox))
    {
      conjName = "axiom" + axiomCnt_;
      axiomCnt_++;
    }
            
    // if it was possible to extra a prefix name, try it        
    if (conjPrefix != null)
    {
      conjName += "_" + conjPrefix.toString();
      // conjPrefix.getWord() is not very good because with names with strokes
      // we need a name visitor here
    }

    // in any case, always have a name for it (e.g., ConjPara with no name)
    if (conjName == null || conjName.isEmpty())
    {
      conjName = "vc" + axiomCnt_;
      axiomCnt_++;
    }
    // add the conjecture name
    assert conjName != null && !conjName.isEmpty() : "Invalid VC conjecture name";
    
    // to avoid naming problems, add vcCnt_ to suffix
    // (e.g., some names with strokes and without like \finsert and \finset_1
    conjName += getVCNameSuffix() + vcCnt_;
    vcCnt_++;

    return conjName;
  }

  /**
   * Each subclass can append a VCName suffix to the conjecture name
   * @return
   */
  protected abstract String getVCNameSuffix();


  @Override
  public Para getVCPara()
  {
    return para_;
  }

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
  public String getInfo()
  {
    // since we cannot retrieve the theorem's name from a latex, neither
    // generate it from a ConjPara, just add some NarrText around instead.
    StringBuilder narrText = new StringBuilder("VC");
    if (!getType().equals(VCType.NONE))
    {
      narrText.append("[");
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
    return narrText.toString();
  }
}
