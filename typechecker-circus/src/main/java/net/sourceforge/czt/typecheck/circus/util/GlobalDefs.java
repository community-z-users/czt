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

import java.util.EnumSet;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.ZName;
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
  
}
