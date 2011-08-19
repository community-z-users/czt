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

import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 * @date Aug 19, 2011
 */
public class DefaultVCNameFactory implements VCNameFactory
{

   private static long axiomCnt_ = 0;

   public static final VCNameFactory DEFAULT_VCNAME_FACTORY = new DefaultVCNameFactory();

  /**
   * For any given Z Paragraph, extract a meaningful name for this VC. It also
   * counts how many axioms there are.
   * @param para
   * @return
   */
  @Override
  public final String createNameForVCOf(Para para, String type)
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
      conjName = conjPrefix.toString();
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
    conjName += type;

    return conjName;
  }
}
