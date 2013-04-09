/*
 GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
 Copyright 2003 Nicholas Daley

 This program is free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License
 as published by the Free Software Foundation; either version 2
 of the License, or (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package net.sourceforge.czt.animation.gui.design.properties.editors;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.FlowLayout;
import java.awt.Frame;
import java.awt.Graphics;
import java.awt.GridBagLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.PropertyEditorSupport;

import javax.swing.BorderFactory;
import javax.swing.ButtonGroup;
import javax.swing.Icon;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JSpinner;
import javax.swing.JTabbedPane;
import javax.swing.JTextField;
import javax.swing.border.BevelBorder;
import javax.swing.border.Border;
import javax.swing.border.CompoundBorder;
import javax.swing.border.EmptyBorder;
import javax.swing.border.EtchedBorder;
import javax.swing.border.LineBorder;
import javax.swing.border.MatteBorder;
import javax.swing.border.SoftBevelBorder;

/**
 * <code>PropertyEditor</code> for <code>Border</code>s.
 * Used in the property editing window for editing <code>Border</code>
 * properties.
 */
public class BorderEditor extends PropertyEditorSupport
{
  private final JDialog chooserDialog;

  private final JLabel exampleBorder = new JLabel()
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 2504427632885810014L;

	protected void paintBorder(Graphics g)
    {
      try {
        super.paintBorder(g);
      } catch (ClassCastException ex) {
        System.err.println("Border is assuming a different component type.");

        setBorder(null);
        super.paintBorder(g);
        //XXX do something here?
      };
    };
  };

  public BorderEditor()
  {
    System.err.println("Started creating border editor");
    chooserDialog = new JDialog((Frame) null, "Border Selector", true);

    try {
      chooserDialog.getContentPane().setLayout(new BorderLayout());

      chooserDialog.getContentPane()
          .add(setupCenterPane(), BorderLayout.CENTER);
      chooserDialog.getContentPane().add(setupExamplePane(), BorderLayout.EAST);
      chooserDialog.getContentPane().add(setupDialogButtonPane(),
          BorderLayout.SOUTH);

      chooserDialog.pack();
    } catch (Exception ex) {
      System.err.println("Exception while making BorderEditor.");
      ex.printStackTrace();
    }
    System.err.println("Finished creating border editor");
  };

  private void clear()
  {
    exampleBorder.setBorder(null);
  };

  private void reset()
  {
    exampleBorder.setBorder((Border) getValue());
  };

  public Component getCustomEditor()
  {
    System.err.println("In getCustomEditor");
    reset();
    System.err.println("Leaving getCustomEditor");
    return chooserDialog;
  };

  public boolean supportsCustomEditor()
  {
    return true;
  };

  private abstract static class SingleBorderEditor extends JPanel
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 4927541139554935774L;

	public abstract Border createBorder();

    public abstract void setEditingBorder(Border border);
  };

  private SingleBorderEditor bevelBorderEditor = new SingleBorderEditor()
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -4592190909362087166L;

	private final JRadioButton raisedButton = new JRadioButton("Raised");

    private final JRadioButton loweredButton = new JRadioButton("Lowered");
    //private Color highlightOuter;
    //private Color highlightInner;
    //private Color shadowOuter;
    //private Color shadowInner;

    {
      setEditingBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));
      setLayout(new GridBagLayout());
      ButtonGroup raisedOrLowered = new ButtonGroup();

      Border raisedBorder = BorderFactory.createBevelBorder(BevelBorder.RAISED);
      raisedButton.setBorder(raisedBorder);
      add(raisedButton);
      raisedOrLowered.add(raisedButton);

      loweredButton.setSelected(true);
      Border loweredBorder = BorderFactory
          .createBevelBorder(BevelBorder.LOWERED);
      loweredButton.setBorder(loweredBorder);
      add(loweredButton);
      raisedOrLowered.add(loweredButton);

      // XXX stuff for setting the colours.
    };

    public Border createBorder()
    {
      if (raisedButton.isSelected())
        return BorderFactory.createBevelBorder(BevelBorder.RAISED);
      // ,highlightOuter,highlightInner,shadowOuter,shadowInner);
      else if (loweredButton.isSelected())
        return BorderFactory.createBevelBorder(BevelBorder.LOWERED);
      // ,highlightOuter,highlightInner,shadowOuter,shadowInner);
      throw new Error("Beveled Borders should be either RAISED or LOWERED");
    };

    public void setEditingBorder(Border border1)
    {
      BevelBorder border = (BevelBorder) border1;
      switch (border.getBevelType()) {
        case BevelBorder.RAISED :
          raisedButton.setSelected(true);
          break;
        case BevelBorder.LOWERED :
          loweredButton.setSelected(true);
          break;
        default : // Not possible.
      };
      //highlightOuter = border.getHighlightOuterColor();
      //highlightInner = border.getHighlightInnerColor();
      //shadowOuter = border.getShadowOuterColor();
      //shadowInner = border.getShadowInnerColor();
    };
  };

  private SingleBorderEditor emptyBorderEditor = new SingleBorderEditor()
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 1005281653507692429L;

	private final JSpinner topS = new JSpinner();

    private final JSpinner leftS = new JSpinner();

    private final JSpinner bottomS = new JSpinner();

    private final JSpinner rightS = new JSpinner();

    {
      setEditingBorder(BorderFactory.createEmptyBorder());
      setLayout(new GridBagLayout());
      add(new JLabel("Top:"));
      add(topS);
      add(new JLabel("Left:"));
      add(leftS);
      add(new JLabel("Bottom:"));
      add(bottomS);
      add(new JLabel("Right:"));
      add(rightS);
    };

    public Border createBorder()
    {
      int top = ((Integer) topS.getValue()).intValue();
      int left = ((Integer) leftS.getValue()).intValue();
      int bottom = ((Integer) bottomS.getValue()).intValue();
      int right = ((Integer) rightS.getValue()).intValue();
      return BorderFactory.createEmptyBorder(top, left, bottom, right);
    };

    public void setEditingBorder(Border border1)
    {
      EmptyBorder border = (EmptyBorder) border1;
      topS.setValue(new Integer(border.getBorderInsets().top));
      leftS.setValue(new Integer(border.getBorderInsets().left));
      bottomS.setValue(new Integer(border.getBorderInsets().bottom));
      rightS.setValue(new Integer(border.getBorderInsets().right));
    };
  };

  private SingleBorderEditor etchedBorderEditor = new SingleBorderEditor()
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 5055680870169708158L;

	private final JRadioButton raisedButton = new JRadioButton("Raised");

    private final JRadioButton loweredButton = new JRadioButton("Lowered");

    private Color highlight;

    private Color shadow;

    {
      setEditingBorder(BorderFactory.createEtchedBorder());
      setLayout(new GridBagLayout());
      ButtonGroup raisedOrLowered = new ButtonGroup();

      Border raisedBorder = BorderFactory
          .createEtchedBorder(EtchedBorder.RAISED);
      raisedButton.setBorder(raisedBorder);
      add(raisedButton);
      raisedOrLowered.add(raisedButton);

      loweredButton.setSelected(true);
      Border loweredBorder = BorderFactory
          .createEtchedBorder(EtchedBorder.LOWERED);
      loweredButton.setBorder(loweredBorder);
      add(loweredButton);
      raisedOrLowered.add(loweredButton);

      //XXX stuff for setting the colours.
    };

    public Border createBorder()
    {
      if (raisedButton.isSelected())
        return BorderFactory.createEtchedBorder(EtchedBorder.RAISED, highlight,
            shadow);
      else if (loweredButton.isSelected())
        return BorderFactory.createEtchedBorder(EtchedBorder.LOWERED,
            highlight, shadow);
      throw new Error("Etched Borders should be either RAISED or LOWERED");
    };

    public void setEditingBorder(Border border1)
    {
      EtchedBorder border = (EtchedBorder) border1;
      switch (border.getEtchType()) {
        case EtchedBorder.RAISED :
          raisedButton.setSelected(true);
          break;
        case EtchedBorder.LOWERED :
          loweredButton.setSelected(true);
          break;
        default : //Not possible
      };
      highlight = border.getHighlightColor();
      shadow = border.getShadowColor();
    };
  };

  private SingleBorderEditor lineBorderEditor = new SingleBorderEditor()
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 307758873346054987L;

	private Color colour;

    private final JSpinner thicknessS = new JSpinner();

    {
      setEditingBorder(BorderFactory.createLineBorder(Color.black));
      setLayout(new GridBagLayout());
      add(new JLabel("Thickness:"));
      add(thicknessS);
    };

    public Border createBorder()
    {
      int thickness = ((Integer) thicknessS.getValue()).intValue();
      return BorderFactory.createLineBorder(colour, thickness);
    };

    public void setEditingBorder(Border border1)
    {
      LineBorder border = (LineBorder) border1;
      colour = border.getLineColor();
      thicknessS.setValue(new Integer(border.getThickness()));
    };
  };

  private SingleBorderEditor matteBorderEditor = new SingleBorderEditor()
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -8830607017064229260L;

	private final JSpinner topS = new JSpinner();

    private final JSpinner leftS = new JSpinner();

    private final JSpinner bottomS = new JSpinner();

    private final JSpinner rightS = new JSpinner();

    private Color colour = null;

    private Icon icon = null;

    {
      setEditingBorder(BorderFactory.createMatteBorder(1, 1, 1, 1, Color.black));
      setLayout(new GridBagLayout());
      add(new JLabel("Top:"));
      add(topS);
      add(new JLabel("Left:"));
      add(leftS);
      add(new JLabel("Bottom:"));
      add(bottomS);
      add(new JLabel("Right:"));
      add(rightS);
      //XXX add stuff for colour
    };

    public Border createBorder()
    {
      if (icon == null && colour == null)
        colour = Color.black;
      int top = ((Integer) topS.getValue()).intValue();
      int left = ((Integer) leftS.getValue()).intValue();
      int bottom = ((Integer) bottomS.getValue()).intValue();
      int right = ((Integer) rightS.getValue()).intValue();
      if (colour == null)
        return BorderFactory.createMatteBorder(top, left, bottom, right, icon);
      else
        return BorderFactory
            .createMatteBorder(top, left, bottom, right, colour);
    };

    public void setEditingBorder(Border border1)
    {
      MatteBorder border = (MatteBorder) border1;
      topS.setValue(new Integer(border.getBorderInsets().top));
      leftS.setValue(new Integer(border.getBorderInsets().left));
      bottomS.setValue(new Integer(border.getBorderInsets().bottom));
      rightS.setValue(new Integer(border.getBorderInsets().right));
      colour = border.getMatteColor();
      icon = border.getTileIcon();
    };
  };

  private SingleBorderEditor softBevelBorderEditor = new SingleBorderEditor()
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 6329395239203748349L;

	private final JRadioButton raisedButton = new JRadioButton("Raised");

    private final JRadioButton loweredButton = new JRadioButton("Lowered");
    //private Color highlightOuter;
    //private Color highlightInner;
    //private Color shadowOuter;
    //private Color shadowInner;

    {
      setEditingBorder(BorderFactory.createBevelBorder(BevelBorder.LOWERED));
      setLayout(new GridBagLayout());
      ButtonGroup raisedOrLowered = new ButtonGroup();

      Border raisedBorder = BorderFactory.createBevelBorder(BevelBorder.RAISED);
      raisedButton.setBorder(raisedBorder);
      add(raisedButton);
      raisedOrLowered.add(raisedButton);

      loweredButton.setSelected(true);
      Border loweredBorder = BorderFactory
          .createBevelBorder(BevelBorder.LOWERED);
      loweredButton.setBorder(loweredBorder);
      add(loweredButton);
      raisedOrLowered.add(loweredButton);

      //XXX stuff for setting the colours.
    };

    public Border createBorder()
    {
      if (raisedButton.isSelected())
        return new SoftBevelBorder(BevelBorder.RAISED);
      //,highlightOuter,highlightInner,shadowOuter,shadowInner);
      else if (loweredButton.isSelected())
        return new SoftBevelBorder(BevelBorder.LOWERED);
      //,highlightOuter,highlightInner,shadowOuter,shadowInner);
      throw new Error("Beveled Borders should be either RAISED or LOWERED");
    };

    public void setEditingBorder(Border border1)
    {
      BevelBorder border = (BevelBorder) border1;
      switch (border.getBevelType()) {
        case BevelBorder.RAISED :
          raisedButton.setSelected(true);
          break;
        case BevelBorder.LOWERED :
          loweredButton.setSelected(true);
          break;
        default : //Not possible
      };
      //highlightOuter = border.getHighlightOuterColor();
      //highlightInner = border.getHighlightInnerColor();
      //shadowOuter = border.getShadowOuterColor();
      //shadowInner = border.getShadowInnerColor();
    };
  };

  private JPanel setupCenterPane()
  {
    final JPanel centerPane = new JPanel();
    final JTabbedPane mainPane;
    final JCheckBox titleCheck;
    final JTextField titleField;
    centerPane.setLayout(new BorderLayout());

    //Setting up the title pane
    {
      final JPanel titlePane = new JPanel();
      titlePane.setLayout(new BorderLayout());
      titleCheck = new JCheckBox("Title:");
      titleField = new JTextField();
      titleField.setEnabled(titleCheck.isSelected());

      titleCheck.addActionListener(new ActionListener()
      {
        public void actionPerformed(ActionEvent ev)
        {
          titleField.setEnabled(titleCheck.isSelected());
        };
      });
      titlePane.add(titleCheck, BorderLayout.WEST);
      titlePane.add(titleField, BorderLayout.CENTER);
      centerPane.add(titlePane, BorderLayout.NORTH);
    }

    centerPane.add(mainPane = setupMainPane(), BorderLayout.CENTER);

    //Setting up the button pane
    {
      final JPanel buttonPane = new JPanel();
      buttonPane.setLayout(new FlowLayout(FlowLayout.CENTER));
      final JButton clearButton = new JButton("Clear Borders");
      clearButton.addActionListener(new ActionListener()
      {
        public void actionPerformed(ActionEvent ev)
        {
          clear();
        };
      });
      buttonPane.add(clearButton);

      final JButton addButton = new JButton("Add Border");
      addButton.addActionListener(new ActionListener()
      {
        public void actionPerformed(ActionEvent ev)
        {
          final SingleBorderEditor editor = (SingleBorderEditor) mainPane
              .getSelectedComponent();
          Border newBorder;
          if (editor == null)
            return;
          newBorder = editor.createBorder();
          if (titleCheck.isSelected())
            newBorder = BorderFactory.createTitledBorder(newBorder, titleField
                .getText());

          if (exampleBorder.getBorder() == null)
            exampleBorder.setBorder(newBorder);
          else {
            Border b = BorderFactory.createCompoundBorder(newBorder,
                exampleBorder.getBorder());
            exampleBorder.setBorder(b);
          };
        }
      });
      buttonPane.add(addButton);

      final JButton removeButton = new JButton("Remove Border");
      removeButton.addActionListener(new ActionListener()
      {
        public void actionPerformed(ActionEvent ev)
        {
          if (exampleBorder.getBorder() instanceof CompoundBorder) {
            CompoundBorder cb = ((CompoundBorder) exampleBorder.getBorder());
            exampleBorder.setBorder(cb.getInsideBorder());
          }
          else {
            exampleBorder.setBorder(null);
          }
        };
      });
      buttonPane.add(removeButton);
      centerPane.add(buttonPane, BorderLayout.SOUTH);
    };
    return centerPane;
  }

  private JTabbedPane setupMainPane()
  {
    JTabbedPane mainPane = new JTabbedPane(JTabbedPane.LEFT);

    mainPane.add("Bevel", bevelBorderEditor);
    mainPane.add("Empty", emptyBorderEditor);
    mainPane.add("Etched", etchedBorderEditor);
    mainPane.add("Line", lineBorderEditor);
    mainPane.add("Matte", matteBorderEditor);
    mainPane.add("SoftBevel", softBevelBorderEditor);

    return mainPane;
  };

  private JPanel setupExamplePane()
  {
    JPanel examplePane = new JPanel();
    examplePane.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
    examplePane.setLayout(new BorderLayout());
    JLabel label = new JLabel("Preview:");
    label.setBorder(BorderFactory.createEmptyBorder(0, 0, 5, 0));
    examplePane.add(label, BorderLayout.NORTH);
    examplePane.add(exampleBorder);
    return examplePane;
  };

  private JPanel setupDialogButtonPane()
  {
    JPanel buttonPane = new JPanel();
    buttonPane.setLayout(new FlowLayout(FlowLayout.CENTER));
    JButton okButton = new JButton("OK");
    okButton.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent ev)
      {
        chooserDialog.setVisible(false);
        setValue(exampleBorder.getBorder());
      };
    });
    buttonPane.add(okButton);

    JButton cancelButton = new JButton("Cancel");
    cancelButton.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent ev)
      {
        chooserDialog.setVisible(false);
        reset();
      };
    });
    buttonPane.add(cancelButton);

    JButton resetButton = new JButton("Reset");
    resetButton.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent ev)
      {
        reset();
      };
    });
    buttonPane.add(resetButton);

    return buttonPane;
  };
};
