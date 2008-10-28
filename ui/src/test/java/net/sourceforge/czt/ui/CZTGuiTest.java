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
    assertEquals(16, czticon.getHeight(null));
    assertEquals(16, czticon.getWidth(null));
  }
}
