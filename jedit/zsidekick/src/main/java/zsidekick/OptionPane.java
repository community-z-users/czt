/*
 * OptionPane.java
 * Copyright (C) 2005, 2006, 2007 Petra Malik
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */
package zsidekick;

import javax.swing.*;
import java.awt.event.*;
import java.awt.*;

import org.gjt.sp.jedit.gui.*;
import org.gjt.sp.jedit.*;

public class OptionPane extends AbstractOptionPane
{
  private final String PRINT_IDS =
    ZSideKickPlugin.PROP_PRINT_IDS;
  private final String IGNORE_UNKNOWN_LATEX_COMMANDS =
    ZSideKickPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS;
  private final String PROP_LABEL_STD_CONFORMANCE =
    ZSideKickPlugin.OPTION_PREFIX + "standardConformance";
  private final String PROP_LABEL_PRINT_IDS =
    ZSideKickPlugin.OPTION_PREFIX + "printNameIds";
  private final String PROP_LABEL_IGNORE_UNKNOWN_LATEX_COMMANDS =
    ZSideKickPlugin.OPTION_PREFIX + "ignoreUnknownLatexCommands";
  private final String PROP_LABEL_RESET =
    ZSideKickPlugin.OPTION_PREFIX + "resetButton";

  private JCheckBox ignoreUnknownLatexCommands_;
  private JCheckBox printIds_;

  public OptionPane()
  {
    super("zsidekick");
  }

  protected void _init()
  {
    addComponent(new JLabel(jEdit.getProperty(PROP_LABEL_STD_CONFORMANCE)));

    String string =
      jEdit.getProperty(PROP_LABEL_IGNORE_UNKNOWN_LATEX_COMMANDS);
    ignoreUnknownLatexCommands_ = new JCheckBox(string);

    boolean value = jEdit.getBooleanProperty(IGNORE_UNKNOWN_LATEX_COMMANDS);
    ignoreUnknownLatexCommands_.getModel().setSelected(value);
    addComponent(ignoreUnknownLatexCommands_);

    printIds_ =
      new JCheckBox(jEdit.getProperty(PROP_LABEL_PRINT_IDS));
    value = jEdit.getBooleanProperty(PRINT_IDS);
    printIds_.getModel().setSelected(value);
    addComponent(printIds_);

    JButton resetButton =
      new JButton(jEdit.getProperty(PROP_LABEL_RESET));
    resetButton.addActionListener(new ResetHandler());
    addComponent(resetButton);
  }

  protected void _save()
  {
    boolean value = ignoreUnknownLatexCommands_.getModel().isSelected();
    jEdit.setBooleanProperty(IGNORE_UNKNOWN_LATEX_COMMANDS, value);
    value = printIds_.getModel().isSelected();
    jEdit.setBooleanProperty(PRINT_IDS, value);
  }

  class ResetHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      printIds_.getModel().setSelected(false);
      ignoreUnknownLatexCommands_.getModel().setSelected(false);
    }
  }
}
