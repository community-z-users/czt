/*
 * CztOptionPane.java
 * Copyright (C) 2005 Petra Malik
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
 
import javax.swing.*;
import java.awt.event.*;
import java.awt.*;
import java.util.Vector;

import net.sourceforge.czt.parser.z.Latex2Unicode;

import org.gjt.sp.jedit.gui.*;
import org.gjt.sp.jedit.*;

public class CztOptionPane extends AbstractOptionPane
{
  private final String SPACE_BEFORE_PUNCTATION =
    CommunityZToolsPlugin.PROP_SPACE_BEFORE_PUNCTATION;
  private final String IGNORE_UNKNOWN_LATEX_COMMANDS =
    CommunityZToolsPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS;
  private final String PROP_LABEL_STD_CONFORMANCE =
    CommunityZToolsPlugin.OPTION_PREFIX + "standardConformance";
  private final String PROP_LABEL_ADD_SPACE_BEFORE_PUNCTATION =
    CommunityZToolsPlugin.OPTION_PREFIX + "addSpaceBeforeLatexPunctation";
  private final String PROP_LABEL_IGNORE_UNKNOWN_LATEX_COMMANDS =
    CommunityZToolsPlugin.OPTION_PREFIX + "ignoreUnknownLatexCommands";
  private final String PROP_LABEL_RESET =
    CommunityZToolsPlugin.OPTION_PREFIX + "resetButton";

  private JCheckBox spaceBeforePunctation_;
  private JCheckBox ignoreUnknownLatexCommands_;

  public CztOptionPane()
  {
    super("czt");
  }

  protected void _init()
  {
    addComponent(new JLabel(jEdit.getProperty(PROP_LABEL_STD_CONFORMANCE)));

    spaceBeforePunctation_ =
      new JCheckBox(jEdit.getProperty(PROP_LABEL_ADD_SPACE_BEFORE_PUNCTATION));
    boolean value = jEdit.getBooleanProperty(SPACE_BEFORE_PUNCTATION);
    spaceBeforePunctation_.getModel().setSelected(value);
    addComponent(spaceBeforePunctation_);

    ignoreUnknownLatexCommands_ =
      new JCheckBox(jEdit.getProperty(PROP_LABEL_IGNORE_UNKNOWN_LATEX_COMMANDS));
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
    boolean value = spaceBeforePunctation_.getModel().isSelected();
    jEdit.setBooleanProperty(SPACE_BEFORE_PUNCTATION, value);
    value = ignoreUnknownLatexCommands_.getModel().isSelected();
    jEdit.setBooleanProperty(IGNORE_UNKNOWN_LATEX_COMMANDS, value);
  }

  class ResetHandler implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      spaceBeforePunctation_.getModel().setSelected(false);
      ignoreUnknownLatexCommands_.getModel().setSelected(false);
    }
  }
}
