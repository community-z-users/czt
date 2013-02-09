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

package net.sourceforge.czt.animation.gui.beans;

import java.awt.Component;
import java.awt.Graphics;
import java.awt.Toolkit;
import java.io.File;
import java.net.MalformedURLException;
import java.net.URL;

import javax.swing.Icon;
import javax.swing.ImageIcon;

/**
 * Icon that has its image taken from a resource/File.
 * So Icon properties can be edited easily.
 * @see net.sourceforge.czt.animation.gui.design.properties.editors.IconEditor
 *      IconEditor
 */
public final class ResourceIcon implements Icon
{
  private final Icon delegate_;

  private final URL url_;

  public ResourceIcon(File resource, Toolkit toolkit)
      throws MalformedURLException
  {
    this(resource.toURI().toURL(), toolkit);
  };

  public ResourceIcon(File resource) throws MalformedURLException
  {
    this(resource.toURI().toURL());
  };

  public ResourceIcon(String resource, Toolkit toolkit)
      throws MalformedURLException
  {
    this(ClassLoader.getSystemResource(resource), toolkit);
  };

  public ResourceIcon(String resource) throws MalformedURLException
  {
    this(ClassLoader.getSystemResource(resource));
  };

  public ResourceIcon(URL resource) throws MalformedURLException
  {
    this(resource, Toolkit.getDefaultToolkit());
  };

  public ResourceIcon(URL resource, Toolkit toolkit)
      throws MalformedURLException
  {
    if (resource == null)
      throw new MalformedURLException();
    url_ = resource;
    delegate_ = new ImageIcon(toolkit.getImage(url_));
  };

  public URL getURL()
  {
    return url_;
  };

  public void paintIcon(Component c, Graphics g, int x, int y)
  {
    delegate_.paintIcon(c, g, x, y);
  };

  public int getIconWidth()
  {
    return delegate_.getIconWidth();
  };

  public int getIconHeight()
  {
    return delegate_.getIconHeight();
  };
};
