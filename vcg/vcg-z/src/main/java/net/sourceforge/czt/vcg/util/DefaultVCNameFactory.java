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
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 * @date Aug 19, 2011
 */
public class DefaultVCNameFactory extends AbstractVCNameFactory
{

  private static long axiomCnt_ = 0;
  public static final VCNameFactory DEFAULT_VCNAME_FACTORY = new DefaultVCNameFactory("_vc", "_vc");
  
  private final String vcSuffix;
  private final String vcSectSuffix;
  
  public DefaultVCNameFactory(String vcSuffix, String vcSectSuffix) {
    this.vcSuffix = vcSuffix;
    this.vcSectSuffix = vcSectSuffix;
  }
  
  private static synchronized final void incrementAxCnt()
  {
	  axiomCnt_++;
  }

  @Override
  protected String getAxDefName(AxPara para)
  {
    assert ZUtils.isAxPara(para) && para.getBox().equals(Box.AxBox);
    incrementAxCnt();
    String result = "axiom" + axiomCnt_;
    return result;
  }

  @Override
  protected String getGenericName(Para para)
  {
    incrementAxCnt();
    String result = "vc" + axiomCnt_;
    return result;
  }

  @Override
  protected String getVCName(Para para, String paraName, String vcType)
  {
    // TODO support the type, e.g. in case of duplicates?
//    if (vcType == null) {
//      vcType = defaultNameExt;
//    }
//    return paraName + "_" + vcType;
    
    return paraName + vcSuffix;
  }

  protected String createAxDefName(AxPara para, String name, String type)
  {
    assert ZUtils.isAxPara(para) && para.getBox().equals(Box.AxBox);
    incrementAxCnt();
    String result = name + axiomCnt_;
    return result;
  }

  @Override
  public String getVCSectionName(String originalSectName)
  {
    return originalSectName + vcSectSuffix;
  }
}
