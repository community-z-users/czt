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

import net.sourceforge.czt.session.SourceLocator;
import org.gjt.sp.jedit.*;

public class OptionPane extends AbstractOptionPane
{
  // property names
  private final String PRINT_IDS =
    ZSideKickPlugin.PROP_PRINT_IDS;
  private final String IGNORE_UNKNOWN_LATEX_COMMANDS =
    ZSideKickPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS;
  private final String USE_BEFORE_DECL =
    ZSideKickPlugin.PROP_USE_BEFORE_DECL;
  private final String USE_STRONG_TYPING =
    ZSideKickPlugin.PROP_USE_STRONG_TYPING;
  private final String DEBUG_ZSIDEKICK =
    ZSideKickPlugin.PROP_DEBUG_ZSIDEKICK;  
  private final String PROP_CZTPATH_ZSIDEKICK =
    ZSideKickPlugin.PROP_CZTPATH;

  // property labels
  private final String PROP_LABEL_STD_CONFORMANCE =      
    ZSideKickPlugin.OPTION_PREFIX + "standardConformance";
  private final String PROP_LABEL_PRINT_IDS =
    ZSideKickPlugin.OPTION_PREFIX + "printNameIds";
  private final String PROP_LABEL_IGNORE_UNKNOWN_LATEX_COMMANDS =
    ZSideKickPlugin.OPTION_PREFIX + "ignoreUnknownLatexCommands";
  private final String PROP_LABEL_USE_BEFORE_DECL =
    ZSideKickPlugin.OPTION_PREFIX + "useBeforeDecl";
  private final String PROP_LABEL_USE_STRONG_TYPING =
    ZSideKickPlugin.OPTION_PREFIX + "useStrongTyping";
  private final String PROP_LABEL_DEBUG_ZSIDEKICK =
    ZSideKickPlugin.OPTION_PREFIX + "debugZsideKick";
  private final String PROP_LABEL_CZTPATH_ZSIDEKICK =
    ZSideKickPlugin.OPTION_PREFIX + "cztPathLabel";
  private final String PROP_LABEL_RESET =
    ZSideKickPlugin.OPTION_PREFIX + "resetButton";
  
  private JCheckBox ignoreUnknownLatexCommands_;
  private JCheckBox printIds_;
  private JCheckBox useBeforeDecl_;
  private JCheckBox useStrongTyping_;
  private JCheckBox debug_;
  private CztPath cztPath_;

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

    useBeforeDecl_ = 
      new JCheckBox(jEdit.getProperty(PROP_LABEL_USE_BEFORE_DECL));
    value = jEdit.getBooleanProperty(USE_BEFORE_DECL);
    useBeforeDecl_.getModel().setSelected(value);
    addComponent(useBeforeDecl_);

    useStrongTyping_ = 
      new JCheckBox(jEdit.getProperty(PROP_LABEL_USE_STRONG_TYPING));
    value = jEdit.getBooleanProperty(USE_STRONG_TYPING);
    useStrongTyping_.getModel().setSelected(value);
    addComponent(useStrongTyping_);
    
    debug_ = new JCheckBox(jEdit.getProperty(PROP_LABEL_DEBUG_ZSIDEKICK));
    value = jEdit.getBooleanProperty(DEBUG_ZSIDEKICK);
    debug_.getModel().setSelected(value);
    addComponent(debug_);    

    JButton resetButton =
      new JButton(jEdit.getProperty(PROP_LABEL_RESET));
    resetButton.addActionListener(new ResetHandler());
    addComponent(resetButton);
    
    JButton cztPathButton = 
      new JButton(jEdit.getProperty(PROP_LABEL_CZTPATH_ZSIDEKICK));
    cztPathButton.addActionListener(new CztPathListener());
    addComponent(cztPathButton);
    
    String paths = jEdit.getProperty(PROP_CZTPATH_ZSIDEKICK);
    if (paths == null || paths.isEmpty()) { paths = ""; }
    cztPath_ = new CztPath(SourceLocator.processCZTPaths(paths));
  }

  @Override
  protected void _save()
  {
    boolean value = ignoreUnknownLatexCommands_.getModel().isSelected();
    jEdit.setBooleanProperty(IGNORE_UNKNOWN_LATEX_COMMANDS, value);
    value = printIds_.getModel().isSelected();
    jEdit.setBooleanProperty(PRINT_IDS, value);
    value = useBeforeDecl_.getModel().isSelected();
    jEdit.setBooleanProperty(USE_BEFORE_DECL, value);
    value = useStrongTyping_.getModel().isSelected();
    jEdit.setBooleanProperty(USE_STRONG_TYPING, value);    
    value = debug_.getModel().isSelected();
    jEdit.setBooleanProperty(DEBUG_ZSIDEKICK, value);    
    String cztPath = cztPath_.buildPathList();
    jEdit.setProperty(PROP_CZTPATH_ZSIDEKICK, cztPath);
    JOptionPane.showMessageDialog(this, cztPath);  
    
    // update section manager properties please. TODO.
  }

  class ResetHandler implements ActionListener
  {
    @Override
    public void actionPerformed(ActionEvent e)
    {
      printIds_.getModel().setSelected(false);
      ignoreUnknownLatexCommands_.getModel().setSelected(false);
      useBeforeDecl_.getModel().setSelected(false);
      useStrongTyping_.getModel().setSelected(false);
      debug_.getModel().setSelected(false);
    }
  }
  
  class CztPathListener implements ActionListener
  {
    public void actionPerformed(ActionEvent e)
    {
      cztPath_.showDialog();            
    }
  }
}
