package czt.animation.gui.design;

import java.awt.*;
import java.beans.*;
import javax.swing.*;
import czt.animation.gui.*;

/**
 * Class to wrap around non-visual beans so that they have a visual representation in the FormDesign.
 * Appears as a label with the bean's class name as its text.
 * @see czt.animation.gui.design.FormDesign
 */
public class BeanWrapper extends JLabel {
  /**
   * The bean this object wraps around.
   */
  protected Object bean;

  /**
   * Creates a bean wrapper without specifying the bean to wrap.  
   */
  public BeanWrapper() {
    this(null);
  };
  /**
   * Creates a bean wrapper around <code>b</code>.
   */
  public BeanWrapper(Object b) {
    setBean(b);
    setBorder(BorderFactory.createLineBorder(Color.black));
  };
  /**
   * Getter function for bean.
   */
  public Object getBean() {
    return bean;
  };
  /**
   * Setter function for bean.
   */
  public void setBean(Object b) {
    bean=b;
    try {//XXX show name property? listener to catch name changes?
      setText(Introspector.getBeanInfo(b.getClass()).getBeanDescriptor().getDisplayName());
    } catch (IntrospectionException e) {
      setText(b.getClass().getName());
    };
    try {
      setToolTipText(Introspector.getBeanInfo(b.getClass()).getBeanDescriptor().getShortDescription());
    } catch (IntrospectionException e) {
    };
  };
};

