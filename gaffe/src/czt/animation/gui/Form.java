package czt.animation.gui;
import java.awt.Component;
import java.beans.beancontext.*;
import java.util.EventListener;
import javax.swing.JPanel;
import javax.swing.event.EventListenerList;

/**
 * A Form constitutes a designable panel, window, or dialog.  Forms are designed by a
 * {@link czt.animation.gui.design.FormDesign FormDesign} object.
 */
public class Form extends JPanel implements BeanContextProxy {
  /**
   * Support class for Bean Context Services.  This is used to
   * <ul>
   *   <li>associate non-Component beans with the form,</li>
   *   <li>provide access to the BSF scripting engine to beans.</li>
   * </ul>
   */
  protected BeanContextServicesSupport bcsSupport=new BeanContextServicesSupport();

  /**
   * Support class for keeping track of listeners.  Especially used for the <code>FormListener</code>s.
   * @see czt.animation.gui.FormEvent
   * @see czt.animation.gui.FormListener
   */
  protected EventListenerList listenerSupport=new EventListenerList();
  
  /**
   * Creates a Form without a name.
   */
  public Form() {
    this(null);
  };
  /**
   * Creates a Form with a name.
   */
  public Form(String name) {
    super(null);
    setName(name);
  };
  /**
   * Allows access to the BeanContext contained in this class.
   * Inherited from BeanContextProxy.
   */
  public BeanContextChild getBeanContextProxy() {
    return bcsSupport;
  };
  
  /**
   * Adds a bean to the form.  Triggers a <code>FormEvent</code> going to the <code>beanAdded</code>
   * function of a listener.
   */
  public void addBean(Object bean) {
    if(bean instanceof Component)
      add((Component)bean);
    bcsSupport.add(bean);
    FormListener[] listeners=(FormListener[])getListeners(FormListener.class);
    
    for(int i=0;i<listeners.length;i++)
      listeners[i].beanAdded(new FormEvent(this,bean,FormEvent.ADDED));
  };

  public boolean removeBean(Object bean) {
    if(!bcsSupport.contains(bean)) return false;
    if(bean instanceof Component) {
      remove((Component)bean);
    };
    bcsSupport.remove(bean);
    FormListener[] listeners=(FormListener[])getListeners(FormListener.class);
    
    for(int i=0;i<listeners.length;i++)
      listeners[i].beanRemoved(new FormEvent(this,bean,FormEvent.REMOVED));
    return true;
  }
  /**
   * Adds a listener for <code>FormEvent</code>.
   */
  public void addFormListener(FormListener l) {
    listenerSupport.add(FormListener.class,l);
  };
  /**
   * Removes a listener for <code>FormEvent</code>.
   */
  public void removeFormListener(FormListener l) {
    listenerSupport.remove(FormListener.class,l);
  };
  /**
   * Returns all of the listeners of class <code>c</code>.
   */
  public EventListener[] getListeners(Class c) {
    return listenerSupport.getListeners(c);
  };
};
//XXX add function removeBean
