package czt.animation.gui.design;

import java.util.EventObject;

/**
 * Event object used by {@link czt.animation.gui.Form Form} to notify listeners when a bean has been 
 * added or removed.
 */
public class FormDesignEvent extends EventObject {
  /**
   * The form that was created/deleted
   */
  protected final FormDesign formDesign;

  /**
   * Value for <code>id</code> indicating whether this event shows that a form was created.
   */
  public static final int CREATED=0;
  /**
   * Value for <code>id</code> indicating whether this event shows that a form was deleted.
   */
  public static final int DELETED=1;
  
  /**
   * Member indicating what type of FormDesignEvent this is.  May be either <code>ADDED</code> or 
   * <code>REMOVED</code>.
   */
  protected final int id;

  /**
   * Create a <code>FormDesignEvent</code> notifying that <code>form</code> has been created/removed.
   */
  public FormDesignEvent(Object source, FormDesign formDesign, int id) {
    super(source);
    this.formDesign=formDesign;
    this.id=id;
  };
  /**
   * Returns the bean.
   */
  public FormDesign getFormDesign() {
    return formDesign;
  };
  /**
   * Returns id.
   */
  public int getId() {
    return id;
  };
};
