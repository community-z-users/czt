package czt.animation.gui;
import java.util.EventObject;

/**
 * Event object used by {@link czt.animation.gui.Form Form} to notify listeners when a bean has been 
 * added or removed.
 */
public class FormEvent extends EventObject {
  /**
   * The bean that was added/removed
   */
  protected final Object bean;

  /**
   * Value for <code>id</code> indicating whether this event shows that a bean was added.
   */
  public static final int ADDED=0;
  /**
   * Value for <code>id</code> indicating whether this event shows that a bean was removed.
   */
  public static final int REMOVED=1;
  
  /**
   * Member indicating what type of FormEvent this is.  May be either <code>ADDED</code> or 
   * <code>REMOVED</code>.
   */
  protected final int id;

  /**
   * Create a <code>FormEvent</code> notifying that <code>bean</code> has been added/removed to/from
   * <code>source</code>.
   */
  public FormEvent(Object source, Object bean, int id) {
    super(source);
    this.bean=bean;
    this.id=id;
  };
  /**
   * Returns the bean.
   */
  public Object getBean() {
    return bean;
  };
  /**
   * Returns id.
   */
  public int getId() {
    return id;
  };
};
