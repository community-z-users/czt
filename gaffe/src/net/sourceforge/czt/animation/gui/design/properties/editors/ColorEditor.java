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

import java.awt.Color;
import java.awt.Component;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Rectangle;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyEditorSupport;

import javax.swing.JColorChooser;
import javax.swing.JDialog;

/**
 * <code>PropertyEditor</code> for <code>Color</code>s.
 * Used in the property editing window for editing <code>Color</code>
 * properties.
 */
public class ColorEditor extends PropertyEditorSupport
{
  private final JDialog chooserDialog_;

  public ColorEditor()
  {
    final JColorChooser colourChooser;
    if (getValue() == null)
      setValue(Color.white);
    colourChooser = new JColorChooser((Color) getValue());

    chooserDialog_ = JColorChooser.createDialog(null, "Colour Selector", true,
        colourChooser, new ActionListener()
        {
          public void actionPerformed(ActionEvent ev)
          {
            setValue(colourChooser.getColor());
          };
        }, null);

    addPropertyChangeListener(new PropertyChangeListener()
    {
      public void propertyChange(PropertyChangeEvent ev)
      {
        colourChooser.setColor((Color) getValue());
      }
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

  public boolean isPaintable()
  {
    return true;
  };

  public void paintValue(Graphics gfx1, Rectangle box)
  {
    Graphics2D gfx = (Graphics2D) gfx1;
    gfx.setPaint((Color) getValue());
    gfx.fill(box);
  };

  public String getAsText()
  {
    Color c = (Color) getValue();
    return "Colour - RGBA(" + c.getRed() + "," + c.getGreen() + ","
        + c.getBlue() + "," + c.getAlpha() + ")";
  };
};
