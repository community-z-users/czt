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

package net.sourceforge.czt.animation.gui.beans;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.beancontext.BeanContextChildSupport;
import java.beans.beancontext.BeanContextServiceAvailableEvent;
import java.beans.beancontext.BeanContextServiceRevokedEvent;
import java.beans.beancontext.BeanContextServices;
import java.io.Serializable;
import java.util.Arrays;
import java.util.TooManyListenersException;
import java.util.Vector;

import net.sourceforge.czt.animation.gui.Form;

import org.apache.bsf.BSFException;
import org.apache.bsf.BSFManager;
import org.apache.bsf.util.StringUtils;

/**
 * A bean (for use in interface designs) for running scripts.  Listens for
 * <code>ActionEvent</code>s, and uses the <code>BSFManager</code> service
 * provided by its bean context to run a script stored in its
 * <code>script</code> property.
 */
public class Script extends BeanContextChildSupport
    implements
      ActionListener,
      Serializable
{
  /**
	 * 
	 */
	private static final long serialVersionUID = -1831656956142764188L;

/**
   * Local reference to the BSFManager used to run the script.  Changed when
   * informed about the service via <code>serviceAvailable</code> and
   * <code>serviceRevoked</code>.
   */
  private BSFManager bsfManager_;

  /**
   * The name of this bean.  Passed on to <code>BSFManager</code> as the
   * <code>source</code> of the script.  May be used by the designer or animator
   * in GAfFE to identify this bean.
   */
  private String name_;

  /**
   * The language the script is in.  Should be a string suitable for passing on
   * to BSFManager.
   * Defaults to "javascript".
   */
  private String language_;

  /**
   * The text of the script.  Should be a script written in the language
   * specified by {@link #language_ language_}.
   */
  private String script_;

  /**
   * Default constructor.  Defaults to no reference to the
   * <code>BSFManager</code>, <code>language_="javascript"</code>,
   * <code>script_=""</code>, <code>name_=null</code>.
   */
  public Script()
  {
    bsfManager_ = null;
    setLanguage("javascript");
    setScript("");
    setName(null);

    addPropertyChangeListener("beanContext", new PropertyChangeListener()
    {
      public void propertyChange(PropertyChangeEvent ev)
      {
        if (ev.getOldValue() != null
            && ev.getOldValue() instanceof BeanContextServices)
          ((BeanContextServices) ev.getOldValue())
              .removeBeanContextServicesListener(Script.this);
        if (ev.getNewValue() != null
            && ev.getNewValue() instanceof BeanContextServices)
          ((BeanContextServices) ev.getNewValue())
              .addBeanContextServicesListener(Script.this);
      };
    });
  };

  /**
   * Constructor.
   * @param script initial value for <code>script</code> property.
   */
  public Script(String script)
  {
    this();
    setScript(script);
  };

  /**
   * Constructor.
   * @param script initial value for <code>script</code> property.
   * @param language initial value for <code>language</code> property.
   */
  public Script(String script, String language)
  {
    this();
    setScript(script);
    setLanguage(language);
  };

  /**
   * Setter method for the {@link #language_ language} property.
   */
  public void setLanguage(String language)
  {
    language_ = language;
  };

  /**
   * Getter method for the {@link #language_ language} property.
   */
  public String getLanguage()
  {
    return language_;
  };

  /**
   * Setter method for the {@link #script_ script} property.
   */
  public void setScript(String script)
  {
    script_ = script;
  };

  /**
   * Getter method for the {@link #script_ script} property.
   */
  public String getScript()
  {
    return script_;
  };

  /**
   * Setter method for the {@link #name_ name} property.
   */
  public void setName(String name)
  {
    name_ = name;
  };

  /**
   * Getter method for the {@link #name_ name} property.
   */
  public String getName()
  {
    return name_;
  };

  /**
   * Invoked when an action occurs.  Runs a script through the BSFManager.
   */
  public void actionPerformed(ActionEvent ev)
  {
    if (bsfManager_ == null) {
      //XXX Do something?
      //error dialog?
      //send message back?
      //make it settable?
      System.err.println("Script bean picked up event before BSFManager "
          + "service had been registered.");
      return;
    }

    //XXX At present in BSF, the arguments are ignored by the javascript engine.
    Form thisForm = null;
    try {
      thisForm = (Form) ((BeanContextServices) getBeanContext()).getService(
          this, this, Form.class, null, this);
    } catch (TooManyListenersException ex) {
      thisForm = null;
    };

    //XXXSo instead we'll cheat a little.
    //XXXIt's a bit nasty, but hopefully future versions of BSF will make this
    //   unnecessary.
    try {
      if (language_.equals("javascript")) {
        String script = "(function (thisForm,thisScript) {"
            + StringUtils.lineSeparator + getScript()
            + StringUtils.lineSeparator + "})(Forms.lookup(\""
            + thisForm.getName() + "\")," + "Forms.lookup(\""
            + thisForm.getName() + "\")" + ".beans["
            + Arrays.asList(thisForm.getBeans()).indexOf(this) + "])";

        System.err.println("################");
        System.err.println(script);
        bsfManager_.exec(getLanguage(), getName(), 0, 1, script);

      }
      else {
        Vector<String> argumentNames = new Vector<String>();
        Vector<Object> arguments = new Vector<Object>();
        argumentNames.add("thisScript");
        arguments.add(this);
        argumentNames.add("thisForm");
        arguments.add(thisForm);
        argumentNames.add("triggerEvent");
        arguments.add(ev);

        bsfManager_.apply(getLanguage(), getName(), 1, 1, getScript(),
            argumentNames, arguments);
      }
    } catch (BSFException ex) {
      //XXX Do something?
      //error dialog?
      //send message back?
      //make it settable?
      System.err.println("Script caught BSFException:");
      System.err.println(ex);
      ex.printStackTrace();
      System.err.println("------");
      ex.getTargetException().printStackTrace();
    };
    return;
  };

  /**
   * Called by this bean's context when a new service is available.  Takes note
   * of the <code>BSFManager</code> provided by the context if this is the
   * service being introduced.
   */
  public void serviceAvailable(BeanContextServiceAvailableEvent bcsae)
  {
    if (bcsae.getServiceClass().equals(BSFManager.class)) {
      try {
        bsfManager_ = (BSFManager) ((BeanContextServices) getBeanContext())
            .getService(this, this, BSFManager.class, null, this);
      } catch (TooManyListenersException ex) {
      }
    }
  };

  /**
   * Called by this bean's context when a service is revoked.  Removes the
   * reference to the <code>BSFManager</code> if this is the service being
   *  revoked.
   */
  public void serviceRevoked(BeanContextServiceRevokedEvent bcsre)
  {
    if (bcsre.getServiceClass().equals(BSFManager.class))
      bsfManager_ = null;
  };
};
