package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import java.awt.geom.Line2D;

import javax.swing.JPanel;

public class PanelCoverage extends JPanel implements IView
{
  // Minimum dimension
  private static final Dimension MIN_COORD_AXIS = new Dimension(760,300);
  //height of pixels
  private static final int TOP_SPACE = 30;
  private static final int BOTTOM_SPACE = 30;
  private static final int LEFT_SPACE = 50;
  private static final int RIGHT_SPACE = 30;
  // Coordinate arrow parameters
  private static final int ARROW_HALF_WIDTH = 6;
  private static final int ARROW_LENGTH = 10;
  // Scale numbers
  private static int m_nScaleNumber = 21;
  private static final int SCALE_LARGE_LENGTH = 6;
  private static final int SCALE_SHORT_LENGTH = 3;
  // String position
  private static final int STRING_Y_AXIS_LEFT_PADDING = 16;
  // Panel object
  private static PanelCoverage m_panel;
  public static PanelCoverage getInstance()
  {
    if(m_panel == null)
      m_panel = new PanelCoverage();
    return m_panel;
  }
  private PanelCoverage()
  {
    this.setBackground(Color.WHITE);
  }
  
  private void drawLine(Graphics2D g, float x, float y)
  {
    
  }
  
  @Override
  protected void paintComponent(Graphics g)
  {
    super.paintComponent(g);
    Dimension size = this.getSize();
    // Limit the minimum size of coordinate system 
    if(size.height<MIN_COORD_AXIS.height)
      size.height = MIN_COORD_AXIS.height;
    if(size.width<MIN_COORD_AXIS.width)
      size.width = MIN_COORD_AXIS.width;

    Graphics2D g2 = (Graphics2D) g;
    g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
        RenderingHints.VALUE_ANTIALIAS_ON);
    g2.setPaint(Color.RED);
    
    g2.setPaint(Color.GREEN);
    
    g2.setPaint(Color.BLUE);
    
    // Draw coordinate
    g2.setPaint(Color.BLACK);
    final int AXIS_HEIGHT = size.height-TOP_SPACE-BOTTOM_SPACE;
    final int AXIS_WIDTH = size.width-RIGHT_SPACE-LEFT_SPACE;
    // Draw axis Y
    g2.draw(new Line2D.Float(LEFT_SPACE, TOP_SPACE, LEFT_SPACE, AXIS_HEIGHT));
    // Draw axis X    
    g2.draw(new Line2D.Float(LEFT_SPACE, AXIS_HEIGHT, AXIS_WIDTH, AXIS_HEIGHT));
    // Draw coordinate arrows
    // Y coordinate arrow
    g2.draw(new Line2D.Float(LEFT_SPACE, TOP_SPACE,
        LEFT_SPACE+ARROW_HALF_WIDTH,TOP_SPACE+ARROW_LENGTH));
    g2.draw(new Line2D.Float(LEFT_SPACE, TOP_SPACE,
        LEFT_SPACE-ARROW_HALF_WIDTH,TOP_SPACE+ARROW_LENGTH));
    // X coordinate arrow
    g2.draw(new Line2D.Float(AXIS_WIDTH, AXIS_HEIGHT,
        AXIS_WIDTH-ARROW_LENGTH,AXIS_HEIGHT+ARROW_HALF_WIDTH));
    g2.draw(new Line2D.Float(AXIS_WIDTH, AXIS_HEIGHT,
        AXIS_WIDTH-ARROW_LENGTH,AXIS_HEIGHT-ARROW_HALF_WIDTH));
    // Draw scale
    // Scale Y
    final int nInternalSpaceY = (AXIS_HEIGHT-ARROW_LENGTH)/PanelCoverage.m_nScaleNumber;
    for(int i=1; i<PanelCoverage.m_nScaleNumber; i++)
    {
      int nScalePos = AXIS_HEIGHT - i*nInternalSpaceY;
      if(i%2==0)
      {
        g2.draw(new Line2D.Float(LEFT_SPACE, nScalePos,
          LEFT_SPACE+SCALE_LARGE_LENGTH,nScalePos));
        g2.drawString(Integer.toString(i/2*10)+"%", STRING_Y_AXIS_LEFT_PADDING, nScalePos);
      }
      else
        g2.draw(new Line2D.Float(LEFT_SPACE, nScalePos,
            LEFT_SPACE+SCALE_SHORT_LENGTH,nScalePos));
    }
    // Scale X
    final int nWalkLength = TestExeModel.getWalkLength();
    int nScaleNum = 0;
    // To set number scales for x coordinate according to random walk length
    float fScaleSpan = 1f;
    if(nWalkLength >= m_nScaleNumber)
    {
      nScaleNum = PanelCoverage.m_nScaleNumber;
      fScaleSpan = (float)nWalkLength/(m_nScaleNumber-1);
      System.out.println("scale #:"+m_nScaleNumber+","+fScaleSpan);
    }
    else
      nScaleNum = nWalkLength+1;

    final int internalSpaceX = (AXIS_WIDTH-ARROW_LENGTH)/PanelCoverage.m_nScaleNumber;
    for(int i=1; i<nScaleNum; i++)
    {
      int nScaleposY = AXIS_HEIGHT;
      int nScaleposX = LEFT_SPACE + i*internalSpaceX;
      if(i%2==0)
        g2.draw(new Line2D.Float(nScaleposX, nScaleposY-SCALE_LARGE_LENGTH,
            nScaleposX,nScaleposY));
      else
        g2.draw(new Line2D.Float(nScaleposX, nScaleposY-SCALE_SHORT_LENGTH,
            nScaleposX,nScaleposY));
      // Draw scale text
      g2.drawString(Integer.toString((int)(fScaleSpan*i)), nScaleposX, nScaleposY+16);
    }
    // Draw coverage line
    boolean[] bCoverage = Parameter.getCoverageOption();
  }
  
  @Override
  public void update(Object data)
  {
    paintComponent(this.getGraphics());
    
  }
}
