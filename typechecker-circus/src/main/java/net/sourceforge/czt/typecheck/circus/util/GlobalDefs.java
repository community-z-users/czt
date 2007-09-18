/*
 * GlobalDefs.java
 *
 * Created on 27 de Junho de 2005, 17:36
 *
 * To change this template, choose Tools | Options and locate the template under
 * the Source Creation and Management node. Right-click the template and choose
 * Open. You can then make changes to the template in the Source Editor.
 */

package net.sourceforge.czt.typecheck.circus.util;

import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Manuela
 */
public class GlobalDefs
  extends net.sourceforge.czt.typecheck.z.util.GlobalDefs
{
  public static final KindOfProcess NORMAL = KindOfProcess.NORMAL;
  public static final KindOfProcess PARAM = KindOfProcess.PARAM;
  public static final KindOfProcess INDEX = KindOfProcess.INDEX;
  public static final KindOfProcess GEN = KindOfProcess.GEN;
  
  public static final boolean compareName(Name n1, Name n2, boolean justNames) {
      boolean result;
      if (n1 != null && n2 != null) {
          if (justNames)          
            result = ZUtils.assertZName(n1).getWord().equals(ZUtils.assertZName(n2).getWord());
          else
            result = n1.equals(n2);
      } else
          result = n1 == null && n2 == null;
      return result;
  }
}
