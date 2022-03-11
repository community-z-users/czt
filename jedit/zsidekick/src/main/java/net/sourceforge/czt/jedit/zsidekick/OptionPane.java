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
package net.sourceforge.czt.jedit.zsidekick;

import javax.swing.*;
import java.awt.event.*;

import net.sourceforge.czt.session.SourceLocator;
import org.gjt.sp.jedit.*;

public class OptionPane extends AbstractOptionPane
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 8263809384758327653L;
private JCheckBox ignoreUnknownLatexCommands_;
  private JCheckBox showCompleteTree_;
  private JCheckBox printIds_;
  private JCheckBox printZEves_;
  private JTextField textWitdh_;
  private JCheckBox useBeforeDecl_;
  private JCheckBox raiseWarnings_;
  private JCheckBox recursiveTypes_;
  private JCheckBox useStrongTyping_;
  private JCheckBox vcgProcessParents_;
  private JCheckBox vcgAddTrivialVC_;
  private JCheckBox vcgApplyTransf_;
  private JCheckBox vcgDCInfixApplies_;
  private JCheckBox vcgFSBAddGSetVC_;
  private JCheckBox vcgFSBAddSchema_;

  private JCheckBox debug_;
  private CztPath cztPath_;

  public OptionPane()
  {
    super("zsidekick");
  }

  @Override
  protected void _init()
  {
    addComponent(new JLabel(jEdit.getProperty("options.net.sourceforge.czt.jedit.zsidekick.standardConformance")));

    String label  = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
              ZSideKickPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS);
    boolean value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS);
    ignoreUnknownLatexCommands_ = new JCheckBox(label);
    ignoreUnknownLatexCommands_.getModel().setSelected(value);
    addComponent(ignoreUnknownLatexCommands_);

    label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
              ZSideKickPlugin.PROP_SHOW_COMPLETE_TREE);
    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_SHOW_COMPLETE_TREE);
    showCompleteTree_ = new JCheckBox(label);
    showCompleteTree_.getModel().setSelected(value);
    addComponent(showCompleteTree_);

    label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
              ZSideKickPlugin.PROP_PRINT_NAME_IDS);
    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_PRINT_NAME_IDS);
    printIds_ = new JCheckBox(label);
    printIds_.getModel().setSelected(value);
    addComponent(printIds_);

    label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
              ZSideKickPlugin.PROP_PRINT_ZEVES);
    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_PRINT_ZEVES);
    printZEves_ = new JCheckBox(label);
    printZEves_.getModel().setSelected(value);
    addComponent(printZEves_);

    label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
              ZSideKickPlugin.PROP_TXT_WIDTH);
    int width = jEdit.getIntegerProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TXT_WIDTH, 80);
    textWitdh_ = new JTextField(ZSideKickPlugin.PROPERTY_PREFIX + // this one is different: see Console.GeneralOptionPane ;-)
              ZSideKickPlugin.PROP_TXT_WIDTH);
    textWitdh_.setText(String.valueOf(width));
    addComponent(new JLabel(label), textWitdh_);

    label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_WARNINGS_OUTPUT);
    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_WARNINGS_OUTPUT);
    raiseWarnings_ = new JCheckBox(label);
    raiseWarnings_.getModel().setSelected(value);
    addComponent(raiseWarnings_);

    label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_RECURSIVE_TYPES);
    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_RECURSIVE_TYPES);
    recursiveTypes_ = new JCheckBox(label);
    recursiveTypes_.getModel().setSelected(value);
    addComponent(recursiveTypes_);

    label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_USE_BEFORE_DECL);
    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_USE_BEFORE_DECL);
    useBeforeDecl_ = new JCheckBox(label);
    useBeforeDecl_.getModel().setSelected(value);
    addComponent(useBeforeDecl_);

    label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_USE_STRONG_TYPING);
    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_USE_STRONG_TYPING);
    useStrongTyping_ = new JCheckBox(label);
    useStrongTyping_.getModel().setSelected(value);
    addComponent(useStrongTyping_);

    label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
              ZSideKickPlugin.PROP_VCG_PROCESS_PARENTS);
    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_VCG_PROCESS_PARENTS);
    vcgProcessParents_ = new JCheckBox(label);
    vcgProcessParents_.getModel().setSelected(value);
    addComponent(vcgProcessParents_);

    label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
              ZSideKickPlugin.PROP_VCG_ADD_TRIVIAL_VC);
    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_VCG_ADD_TRIVIAL_VC);
    vcgAddTrivialVC_ = new JCheckBox(label);
    vcgAddTrivialVC_.getModel().setSelected(value);
    addComponent(vcgAddTrivialVC_);

    label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
              ZSideKickPlugin.PROP_VCG_APPLY_TRANSFORMERS);
    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_VCG_APPLY_TRANSFORMERS);
    vcgApplyTransf_ = new JCheckBox(label);
    vcgApplyTransf_.getModel().setSelected(value);
    addComponent(vcgApplyTransf_);

    label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
              ZSideKickPlugin.PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO);
    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO);
    vcgDCInfixApplies_ = new JCheckBox(label);
    vcgDCInfixApplies_.getModel().setSelected(value);
    addComponent(vcgDCInfixApplies_);
    
    label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
            ZSideKickPlugin.PROP_VCG_FEASIBILITY_ADD_GIVENSET_VCS);
  value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_FEASIBILITY_ADD_GIVENSET_VCS);
  vcgFSBAddGSetVC_ = new JCheckBox(label);
  vcgFSBAddGSetVC_.getModel().setSelected(value);
  addComponent(vcgFSBAddGSetVC_);


  label = jEdit.getProperty(ZSideKickPlugin.OPTION_PREFIX +
          ZSideKickPlugin.PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS);
	value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
	          ZSideKickPlugin.PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS);
	vcgFSBAddSchema_ = new JCheckBox(label);
	vcgFSBAddSchema_.getModel().setSelected(value);
	addComponent(vcgFSBAddSchema_);


    label = jEdit.getProperty("options.net.sourceforge.czt.jedit.zsidekick.resetButton");
    JButton resetButton = new JButton(label);
    resetButton.addActionListener(new ResetHandler());
    addComponent(resetButton);

    label = jEdit.getProperty("options.net.sourceforge.czt.jedit.zsidekick.debugZsideKick");
    value = jEdit.getBooleanProperty("net.sourceforge.czt.jedit.zsidekick.debugZsideKick");
    debug_ = new JCheckBox(label);
    debug_.getModel().setSelected(value);
    addComponent(debug_);

    label = jEdit.getProperty("options.net.sourceforge.czt.jedit.zsidekick.cztPathLabel");
    JButton cztPathButton = new JButton(label);
    cztPathButton.addActionListener(new CztPathListener());
    addComponent(cztPathButton);
    
    String paths = jEdit.getProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_CZTPATH);
    if (paths == null || paths.isEmpty()) { paths = ""; }
    cztPath_ = new CztPath(SourceLocator.processCZTPaths(paths));
  }

  @Override
  protected void _save()
  {
    boolean value = ignoreUnknownLatexCommands_.getModel().isSelected();
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS, value);

    value = showCompleteTree_.getModel().isSelected();
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_SHOW_COMPLETE_TREE, value);

    value = printIds_.getModel().isSelected();
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_PRINT_NAME_IDS, value);

    value = printZEves_.getModel().isSelected();
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_PRINT_ZEVES, value);

    String widthStr = textWitdh_.getText();
		if(widthStr != null && widthStr.length() > 0)
			jEdit.setProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TXT_WIDTH, String.valueOf(Integer.valueOf(widthStr)));
		else
			jEdit.unsetProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TXT_WIDTH);

    value = useBeforeDecl_.getModel().isSelected();
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_USE_BEFORE_DECL, value);

    value = raiseWarnings_.getModel().isSelected();
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_WARNINGS_OUTPUT, value);

    value = recursiveTypes_.getModel().isSelected();
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_RECURSIVE_TYPES, value);

    value = useStrongTyping_.getModel().isSelected();
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_TYPECHECK_USE_STRONG_TYPING, value);

    value = vcgProcessParents_.getModel().isSelected();
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_PROCESS_PARENTS, value);

    value = vcgAddTrivialVC_.getModel().isSelected();
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_ADD_TRIVIAL_VC, value);

    value = vcgApplyTransf_.getModel().isSelected();
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_APPLY_TRANSFORMERS, value);

    value = vcgDCInfixApplies_.getModel().isSelected();
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO, value);

    value = debug_.getModel().isSelected();
    jEdit.setBooleanProperty("net.sourceforge.czt.jedit.zsidekick.debugZsideKick", value);

    String cztPath = cztPath_.buildPathList();
    jEdit.setProperty(ZSideKickPlugin.PROPERTY_PREFIX + 
            ZSideKickPlugin.PROP_CZTPATH, cztPath);
  }

  class ResetHandler implements ActionListener
  {
    @Override
    public void actionPerformed(ActionEvent e)
    {
      printIds_.getModel().setSelected(false);
      ignoreUnknownLatexCommands_.getModel().setSelected(false);
      recursiveTypes_.getModel().setSelected(false);
      useStrongTyping_.getModel().setSelected(false);
      debug_.getModel().setSelected(false);
    }
  }
  
  class CztPathListener implements ActionListener
  {
    @Override
    public void actionPerformed(ActionEvent e)
    {
      cztPath_.showDialog();            
    }
  }
}
