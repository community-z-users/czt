/*
  GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
  Copyright 2003 Nicholas Daley
  
  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.
  
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
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

/**
 * A bean (for use in interface designs) for running scripts.  Listens for <code>ActionEvent</code>s,
 * and uses the <code>BSFManager</code> service provided by its bean context to run a script stored in
 * its <code>script</code> property.
 */
public class ScriptDelegate extends BeanContextChildSupport implements ActionListener, Serializable {
  /**
   * Local reference to the BSFManager used to run the script.  Changed when informed about the service
   * via <code>serviceAvailable</code> and <code>serviceRevoked</code>.
   */
  private BSFManager bsfManager;
  
  /**
   * The language the script is in.  Should be a string suitable for passing on to BSFManager.  
   * Defaults to "javascript".  
   */
  private String language;
  /**
   * Setter method for the {@link #language language} property.
   */
  public void setLanguage(String language) {
    this.language=language;
  };
  /**
   * Getter method for the {@link #language language} property.
   */
  public String getLanguage() {
    return language;
  };
  
  /**
   * The text of the script.  Should be a script written in the language specified by 
   * {@link #language language}.
   */
  private String script;
  /**
   * Setter method for the {@link #script script} property.
   */
  public void setScript(String script) {
    this.script=script;
  };
  /**
   * Getter method for the {@link #script script} property.
   */
  public String getScript() {
    return script;
  };

  /**
   * The name of this bean.  Passed on to <code>BSFManager</code> as the <code>source</code> of the
   * script.  May be used by the designer or animator in GAfFE to identify this bean.
   */
  private String name;
  /**
   * Setter method for the {@link #name name} property.
   */
  public void setName(String name) {
    this.name=name;
  };
  /**
   * Getter method for the {@link #name name} property.
   */
  public String getName() {
    return name;
  };
  
  /**
   * Default constructor.  Defaults to no reference to the <code>BSFManager</code>, 
   * <code>language="javascript"</code>, <code>script=""</code>, <code>name=null</code>.
   */
  public ScriptDelegate() {
    bsfManager=null;
    setLanguage("javascript");
    setScript("");
    setName(null);
  };
  
  /**
   * Invoked when an action occurs.  Runs a script through the BSFManager.
   */
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

  /**
   * Called by this bean's context when a new service is available.  Takes note of the 
   * <code>BSFManager</code> provided by the context if this is the service being introduced.
   */
  public void serviceAvailable(BeanContextServiceAvailableEvent bcsae) {
    if(bcsae.getServiceClass().equals(BSFManager.class)) {
      try {
	bsfManager=(BSFManager)bcsae.getSourceAsBeanContextServices()
	  .getService(this,this,BSFManager.class,null,this);
      } catch (TooManyListenersException ex) {}
    }
  };
  /**
   * Called by this bean's context when a service is revoked.  Removes the reference to the 
   * <code>BSFManager</code> if this is the service being revoked.
   */
 