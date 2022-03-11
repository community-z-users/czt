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

import java.awt.Component;
import java.awt.Frame;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.PropertyEditorSupport;
import java.net.MalformedURLException;

import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JOptionPane;

import net.sourceforge.czt.animation.gui.beans.ResourceIcon;

/**
 * <code>PropertyEditor</code> for <code>Icon</code>s.
 * Used in the property editing window for editing <code>Icon</code>
 * properties.
 */
public class IconEditor extends PropertyEditorSupport
{
  private final JDialog chooserDialog_;

  private final JFileChooser chooser_;

  public IconEditor()
  {
    chooser_ = new JFileChooser();
    chooser_.setDialogType(JFileChooser.OPEN_DIALOG);
    chooser_.setApproveButtonText("Load Icon");
    chooser_.setFileSelectionMode(JFileChooser.FILES_ONLY);

    chooserDialog_ = new JDialog((Frame) null, "Load Icon Image", true);
    chooserDialog_.getContentPane().add(chooser_);
    chooserDialog_.pack();

    chooser_.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent ev)
      {
        chooserDialog_.setVisible(false);
        if (ev.getActionCommand().equals(JFileChooser.APPROVE_SELECTION))
          try {
            setValue(new ResourceIcon(chooser_.getSelectedFile()));
          } catch (MalformedURLException ex) {
            JOptionPane.showMessageDialog(chooser_, "Couldn't load icon "
                + "image.  File name produced " + "malformed URL.",
                "Error opening icon image", JOptionPane.ERROR_MESSAGE);
            System.err.println(ex);
            ex.printStackTrace();
          }
      };
    });
  };

  public Component getCustomEditor()
  {
    return chooserDialog_;
  };

  public boolean supportsCustomEditor()
  {
    return true;
  };
};
