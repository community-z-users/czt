package czt.animation.gui.scripting;
import com.ibm.bsf.BSFException;
import com.ibm.bsf.BSFManager;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.beancontext.BeanContextChildSupport;
import java.beans.beancontext.BeanContextServiceAvailableEvent;
import java.beans.beancontext.BeanContextServiceRevokedEvent;
import java.io.Serializable;
import java.util.TooManyListenersException;

public class ScriptDelegate extends BeanContextChildSupport implements ActionListener, Serializable {
  private BSFManager bsfManager;
  
  private String language;
  public void setLanguage(String language) {
    this.language=language;
  };
  public String getLanguage() {
    return language;
  };
  
  private String script;
  public void setScript(String script) {
    this.script=script;
  };
  public String getScript() {
    return script;
  };

  private String name;
  public void setName(String name) {
    this.name=name;
  };
  public String getName() {
    return name;
  };
  
  public ScriptDelegate() {
    bsfManager=null;
    setLanguage("javascript");
    setScript("");
    setName(null);
  };
  
  public void actionPerformed(ActionEvent e) {
    if(bsfManager==null) {
      //XXX Do something?
      //error dialog?
      //send message back?
      //make it settable?
      System.err.println("ScriptDelegate bean picked up event before BSFManager service had been "
			 +"registered.");
      return;
    }
    try {
      bsfManager.exec(getLanguage(),getName(),0,0,getScript());
    } catch (BSFException ex) {
      //XXX Do something?
      //error dialog?
      //send message back?
      //make it settable?
      System.err.println("ScriptDelegate caught BSFException:");
      System.err.println(ex);
    };
    return;
  };

  public void serviceAvailable(BeanContextServiceAvailableEvent bcsae) {
    if(bcsae.getServiceClass().equals(BSFManager.class)) {
      try {
	bsfManager=(BSFManager)bcsae.getSourceAsBeanContextServices()
	  .getService(this,this,BSFManager.class,null,this);
      } catch (TooManyListenersException ex) {}
    }
  };
  public void serviceRevoked(BeanContextServiceRevokedEvent bcsre) {
    if(bcsre.getServiceClass().equals(BSFManager.class))
      bsfManager=null;
  };
  
};





