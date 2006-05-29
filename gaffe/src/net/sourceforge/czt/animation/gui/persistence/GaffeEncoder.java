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

package net.sourceforge.czt.animation.gui.persistence;

import java.beans.Statement;
import java.beans.XMLEncoder;
import java.io.OutputStream;
import java.util.EventListener;

/**
 * An <code>XMLEncoder</code> that strips registration of listeners.
 * Because listeners are stored in a seperate <code>Vector</code> of
 * {@link net.sourceforge.czt.animation.gui.design.BeanLink BeanLink}s, and any
 * listeners registered with a bean are part of the designer/generator, we don't
 * want listeners to be saved.
 */
public class GaffeEncoder extends XMLEncoder
{
  /**
   * Constructor for new encoder sending beans to <code>os</code>.
   * @param os {@inheritDoc}
   */
  public GaffeEncoder(OutputStream os)
  {
    super(os);
  };

  /**
   * Overridden <code>writeStatement</code>.  Strips any statements with a
   * method name of the form add*Listener, with an EventListener (from the
   * relevant places in Gaffe) as its only argument.
   * @param stat {@inheritDoc}
   */
  public void writeStatement(Statement stat)
  {
    if (stat.getMethodName().startsWith("add")
        && stat.getMethodName().endsWith("Listener")
        && stat.getArguments().length == 1
        && stat.getArguments()[0] instanceof EventListener) {
      String paramClassName = stat.getArguments()[0].getClass().getName();
      final String gaffePackage = "net.sourceforge.czt.animation.gui";
      if (paramClassName.startsWith(gaffePackage + ".Form$")
          || paramClassName.startsWith(gaffePackage + ".design"))
        return;
    };
    super.writeStatement(stat);
  };
};
