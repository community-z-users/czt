package net.sourceforge.czt.eclipse.zeves.core;

import net.sourceforge.czt.eclipse.zeves.core.internal.ZEvesCorePlugin;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot;

/**
 * @author Andrius Velykis
 */
public class ZEvesCore
{
  public static ZEves getZEves() {
    return ZEvesCorePlugin.getZEves();
  }
  
  public static ZEvesSnapshot getSnapshot() {
    return getZEves().getSnapshot();
  }
  
  
}
