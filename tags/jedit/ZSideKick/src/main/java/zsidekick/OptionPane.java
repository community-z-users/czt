/*
 * OptionPane.java
 * Copyright (C) 2005, 2006 Petra Malik
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
  private final String EXTRACT_COMMA_OR_SEMI =
    ZSideKickPlugin.PROP_EXTRACT_COMMA_OR_SEMI_FROM_DECORWORDS;
  private final String IGNORE_UNKNOWN_LATEX_COMMANDS =
    ZSideKickPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS;
  private final String PROP_LABEL_STD_CONFORMANCE =
    ZSideKickPlugin.OPTION_PREFIX + "standardConformance";
  private final String PROP_LABEL_EXTRACT_COMMA_OR_SEMI =
    ZSideKickPlugin.OPTION_PREFIX + "extractCommaOrSemi";
  private final String PROP_LABEL_IGNORE_UNKNOWN_LATEX_COMMANDS =
    ZSideKickPlugin.OPTION_PREFIX + "ignoreUnknownLatexCommands";
  private final String PROP_LABEL_RESET =
    ZSideKickPlugin.OPTION_PREFIX + "resetButton";

  private JCheckBox extractCommaOrSemi_;
  private JCheckBox spaceBeforePunctation_;
  private JCheckBox ignoreUnknownLatexCommands_;

  public OptionPane()
  {
    super("zsidekick");
  }

  protected void _init()
  {
    addComponent(new JLabel(jEdit.getProperty(PROP_LABEL_STD_CONFORMANCE)));

    extractCommaOrSemi_ =
      new JCheckBox(jEdit.getProperty(PROP_LABEL_EXTRACT_COMMA_OR_SEMI));
    boolean value = jEdit.getBooleanProperty(EXTRACT_COMMA_OR_SEMI);
    extractCommaOrSemi_.getModel().setSelected(value);
    addComponent(extractCommaOrSemi_);

    String string =
      jEdit.getProperty(PROP_LABEL_IGNORE_UNKNOWN_LATEX_COMMANDS);
    ignoreUnknownLatexCommands_ = new JCheckBox(string);

    value = jEdit.getBooleanProperty(IGNORE_UNKNOWN_LATEX_COMMANDS);
    ignoreUnknownLatexCommands_.getModel().setSelected(value);
    addComponent(ignoreUnknownLatexCommands_);

    JButton resetButton =
      new JButton(jEdit.getProperty(PROP_LABEL_RESET));
    resetButton.addActionListener(new ResetHandler());
    addComponent(resetButton);
  }

  protected void _save()
  {
    boolean value = extractCommaOrSemi_.getModel().isSelected();
    jEdit.setBooleanProperty(EXTRACT_COMMA_OR_SEMI, value);
    value = ignoreUnknownLatexCommands_.getModel().isSelected();
    jEdit.setBooleanProperty(IGNORE_UNKNOWN_LATEX_COMMANDS, value);
  }

  class ResetHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      extractCommaOrSemi_.getModel().setSelected(false);
      spaceBeforePunctation_.getModel().setSelected(false);
      ignoreUnknownLatexCommands_.getModel().setSelected(false);
    }
  }
}
