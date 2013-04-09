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
package net.sourceforge.czt.vcg.util;

import java.util.List;

import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 * @author Andrius Velykis
 * @date Aug 19, 2011
 */
public abstract class AbstractVCNameFactory implements VCNameFactory
{

  // for Operator names, we need something else for the underscores
  public static String createZNameAsString(ZName zname)
  {
    String result = ZUtils.toStringZName(zname);
    //OperatorName on = zname.getOperatorName();
    //if (on != null)
    //{
      result = cleanPossibleNameParameters(result);
    //}
    return result;
  }

  public static String cleanPossibleNameParameters(String zname)
  {
    String result = zname.replaceAll(ZString.LISTARG, "LARG");
    result = result.replaceAll(ZString.ARG, "ARG");
    return result;
  }

  protected String getAbbreviationName(AxPara para)
  {
    assert ZUtils.isAbbreviation(para);
    return createZNameAsString(ZUtils.assertZName(ZUtils.getAbbreviationName(para)));
  }

  protected String getSchemaName(AxPara para)
  {
    assert ZUtils.isSimpleSchema(para);
    return createZNameAsString(ZUtils.assertZName(ZUtils.getSchemaName(para)));
  }

  protected String getFreeParaName(FreePara para)
  {
    return createZNameAsString(ZUtils.assertZFreetypeList(para.getFreetypeList()).get(0).getZName());
  }
  
  protected String getGivenParaName(GivenPara para)
  {
    List<Name> givenNames = para.getNames();
    if (givenNames.isEmpty()) {
      return null;
    }
    
    // use the first name - it will uniquely identify the whole given para
    return createZNameAsString(ZUtils.assertZName(givenNames.get(0)));
  }

  protected String getConjParaName(ConjPara para)
  {
    return para.getName();
  }

  protected abstract String getAxDefName(AxPara para);
  
  protected abstract String getGenericName(Para para);
  
  protected abstract String getVCName(Para para, String paraName, String vcType);

  /**
   * For any given Z Paragraph, extract a meaningful name for this VC. 
   * 
   * @param para
   * @param type
   * @return
   */
  @Override
  public String getVCName(Para para, String type)
  {
    // create the conjecture name or internal axiom name
    String paraName = null;
    
    if (ZUtils.isAbbreviation(para))
    {
      paraName = getAbbreviationName((AxPara) para);
    }
    else if (ZUtils.isSimpleSchema(para))
    {
      paraName = getSchemaName((AxPara) para);
    }
    else if (para instanceof ConjPara)
    {
      paraName = getConjParaName((ConjPara) para);
    }
    else if (para instanceof FreePara)
    {
      // for multiple free types, just get the first name available.
      paraName = getFreeParaName((FreePara) para);
    }
    else if (para instanceof GivenPara)
    {
      paraName = getGivenParaName((GivenPara) para);
    }
    else if (ZUtils.isAxPara(para) && ((AxPara) para).getBox().equals(Box.AxBox))
    {
      paraName = getAxDefName((AxPara) para);
    }

    // in any case, always have a name for it (e.g., ConjPara with no name)
    if (paraName == null || paraName.isEmpty())
    {
      paraName = getGenericName(para);
    }
    
    // add the conjecture name
    assert paraName != null && !paraName.isEmpty() : "Invalid VC conjecture name";

    return getVCName(para, paraName, type);
  }
  
}
