package czt.animation.gui.design;

import java.util.EventListener;

/**
 * Listener for {@link czt.animation.gui.FormEvent FormEvent}s.
 */
public interface FormDesignListener extends EventListener {
  /**
   * Called when a form is created.
   */
  public void formCreated(FormDesignEvent e);
  /**
   * Called when a form is deleted.
   */
  public void formDeleted(FormDesignEvent e);
};
