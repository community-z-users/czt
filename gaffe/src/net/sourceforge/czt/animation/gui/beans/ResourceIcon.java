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

import java.net.URL;
import java.net.MalformedURLException;

import javax.swing.Icon;
import javax.swing.ImageIcon;


public final class ResourceIcon implements Icon {
  private Icon delegate;
  private URL url;
  
  public ResourceIcon(File resource, Toolkit toolkit) throws MalformedURLException {
    this(resource.toURL(),toolkit);
  };
  public ResourceIcon(File resource) throws MalformedURLException {
    this(resource.toURL());
  };
  public ResourceIcon(String resource, Toolkit toolkit) throws MalformedURLException {
    this(ClassLoader.getSystemResource(resource),toolkit);
  };
  public ResourceIcon(String resource) throws MalformedURLException {
    this(ClassLoader.getSystemResource(resource));
  };
  public ResourceIcon(URL resource) throws MalformedURLException {
    this(resource,Toolkit.getDefaultToolkit());
  };
  public ResourceIcon(URL resource, Toolkit toolkit) throws MalformedURLException {
    if(resource==null) throw new MalformedURLException();
    url=resource;
    delegate=new ImageIcon(toolkit.getImage(url));
  };
  
  public URL getURL() {return url;};

  public void paintIcon(Component c, Graphics g, int x, int y) {delegate.paintIcon(c,g,x,y);};
  public int getIconWidth()  {return delegate.getIconWidth();};
  public int getIconHeight() {return delegate.getIconHeight();};
};
