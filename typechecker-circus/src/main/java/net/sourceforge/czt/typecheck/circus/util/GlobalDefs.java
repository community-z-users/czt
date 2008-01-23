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
import net.sourceforge.czt.circus.ast.CommPattern;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
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

  
  /**
   * This is a convenience method. It filters the getUsedCommunications() communication list
   * so that, within each Communication in the list, we extract the underlying channel name and
   * type for that communication (if present). Note this may include implicit and generic channels. 
   * If no type annotation is available, the signature just contains a list of names.
   */
  public static Signature getUsedChannels(CommunicationList commList)
  {
    // 
    return null;
//    for(Communication comm : getUsedCommunications())
//    {
//    }
  }
  
  /**
   * This is a convenience method. It filters the getUsedCommunications() communication list
   * so that, within each Communication in the list, we extract the underlying channel name 
   * for hat communication (if present). Note this may include generic channels. 
   * Implicit channels have the index added to their names.
   */
  public static Map<CommPattern, ZNameList> getAlphabet()
  {
    return null;
  }
  
  // expand scopes of local vars within aSig ?
  //public static flattenLocalVariables(ActionSignature aSig)
  
}
