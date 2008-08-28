package net.sourceforge.czt.modeljunit.gui;

import javax.swing.JPanel;

/** The superclass of all top-level tabs of the GUI.
 *  This defines methods for resetting the model etc.
 *  
 * @author marku
 *
 */
@SuppressWarnings("serial")
public abstract class PanelAbstract extends JPanel
{
  /** Tell the tab that the model has changed */
  public abstract void newModel();
}
