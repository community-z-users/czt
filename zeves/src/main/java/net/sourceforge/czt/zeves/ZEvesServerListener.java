package net.sourceforge.czt.zeves;

import java.util.EventListener;

public interface ZEvesServerListener extends EventListener
{

  public void serverStarted(ZEvesServerEvent event);
  
  public void serverStopped(ZEvesServerEvent event);
  
}
