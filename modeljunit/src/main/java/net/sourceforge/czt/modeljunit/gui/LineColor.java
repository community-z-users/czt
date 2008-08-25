
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;

/*
 * Data structure of line chart for display coverage
 */
public class LineColor
{
  public LineColor(String strCov, Color color)
  {
    m_strCoverage = strCov;
    m_color = color;
  }

  public String m_strCoverage;

  public Color m_color;
}
