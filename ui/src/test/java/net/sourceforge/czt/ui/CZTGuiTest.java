package net.sourceforge.czt.ui;

import java.awt.Image;
import java.net.URL;

import javax.swing.ImageIcon;

import junit.framework.TestCase;

public class CZTGuiTest extends TestCase
{
  public void testIcon()
  {
    URL iconurl = this.getClass().getResource("images/CZTicon.png");
    assertNotNull(iconurl);
    ImageIcon icon = new ImageIcon(iconurl);
    Image czticon = icon.getImage();
    assertNotNull(czticon);
    System.out.println("CZT Icon height = "+czticon.getHeight(null));
    assertEquals(17, czticon.getHeight(null));
  }
}
