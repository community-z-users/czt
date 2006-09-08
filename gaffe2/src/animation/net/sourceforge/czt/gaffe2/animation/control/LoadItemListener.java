/**
 * 
 */

package net.sourceforge.czt.gaffe2.animation.control;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.XMLDecoder;
import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;

import javax.swing.JFileChooser;
import javax.swing.tree.DefaultTreeModel;

import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.gaffe2.animation.common.factory.GaffeFactory;
import net.sourceforge.czt.gaffe2.animation.model.Step;
import net.sourceforge.czt.gaffe2.animation.model.StepTree;
import net.sourceforge.czt.gaffe2.animation.view.MainFrame;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.z.ast.Expr;

/**
 * @author Linan Zhang
 *
 */
public class LoadItemListener implements ActionListener
{
  /**
   * 
   */
  public LoadItemListener()
  {
  }

  /* (non-Javadoc)
   * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
   */
  public void actionPerformed(ActionEvent arg0)
  {
    MainFrame parent = MainFrame.getMainFrame();
    JFileChooser fileChooser = new JFileChooser("load ..");
    if (fileChooser.showOpenDialog(parent) == JFileChooser.APPROVE_OPTION) {
      this.load(fileChooser.getSelectedFile());
    }
  }

  /**
   * @param file
   */
  public void load(File file)
  {
    try {
      XMLDecoder e = new XMLDecoder(new BufferedInputStream(
          new FileInputStream(file)));
      DefaultTreeModel stepTree = (DefaultTreeModel) e.readObject();
      StepTree.setStepTree(stepTree);
      StepTree.setCurrentStep((Step) stepTree.getRoot());
      e.close();
    } catch (IOException ioex) {
      ioex.printStackTrace();
    }
  }

  public Expr toExpr(String value)
  {
    Source newSource = new StringSource(value);
    newSource.setMarkup(Markup.LATEX);
    ZLive zLive = GaffeFactory.getZLive();
    SectionManager sectman = zLive.getSectionManager();
    //String name of section
    try {
      Expr expr = ParseUtils.parseExpr(newSource, zLive.getCurrentSection(),
          sectman);
      return expr;
    } catch (IOException ex) {
      ex.printStackTrace();
      return null;
    } catch (CommandException ex) {
      ex.printStackTrace();
      return null;
    }
  }
}
