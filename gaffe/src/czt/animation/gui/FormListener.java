package czt.animation.gui;

import java.util.EventListener;

/**
 * Listener for {@link czt.animation.gui.FormEvent FormEvent}s.
 */
public interface FormListener extends EventListener {
  /**
   * Called when a bean is added to a form.
   */
  public void beanAdded(FormEvent e);
  /**
   * Called when a bean is removed from a form.
   */
  public void beanRemoved(FormEvent e);
};
