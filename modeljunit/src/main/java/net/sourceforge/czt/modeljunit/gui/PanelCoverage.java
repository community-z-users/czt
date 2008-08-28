
package net.sourceforge.czt.modeljunit.gui;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import java.awt.geom.Line2D;
import java.util.ArrayList;

import javax.swing.JPanel;

public class PanelCoverage extends PanelAbstract
{
  private static final long serialVersionUID = 145722827927748022L;

  // Minimum dimension
  private static final Dimension MIN_COORD_AXIS = new Dimension(760, 300);

  //height of pixels
  private static final int TOP_SPACE = 30;

  private static final int BOTTOM_SPACE = 30;

  private static final int LEFT_SPACE = 50;

  private static final int RIGHT_SPACE = 30;

  // Coordinate arrow parameters
  private static final int ARROW_HALF_WIDTH = 6;

  private static final int ARROW_LENGTH = 10;

  // Scale numbers
  private static int m_nScaleNumber = 20;

  private static final int SCALE_LARGE_LENGTH = 6;

  private static final int SCALE_SHORT_LENGTH = 3;

  private int[] m_arrayStages = null;

  // String position
  private static final int STRING_Y_AXIS_LEFT_PADDING = 16;

  // Points to draw
  // State coverage array
  private ArrayList<Integer> m_covS;

  // Transition coverage array
  private ArrayList<Integer> m_covT;

  // Transition pair coverage array
  private ArrayList<Integer> m_covTP;

  // Action coverage array
  private ArrayList<Integer> m_covA;

  // Panel object
  private static PanelCoverage m_panel;

  public static PanelCoverage getInstance()
  {
    if (m_panel == null)
      m_panel = new PanelCoverage();
    return m_panel;
  }

  private PanelCoverage()
  {
    this.setBackground(Color.WHITE);
    this.setDoubleBuffered(true);
  }

  /**
   * To get how many times the test has to run to draw the line chart
   * */
  public int[] getStages()
  {
    return m_arrayStages;
  }

  @Override
  protected void paintComponent(Graphics g)
  {
    super.paintComponent(g);
    Dimension size = getSize();
    // Limit the minimum size of coordinate system
    if (size.height < MIN_COORD_AXIS.height)
      size.height = MIN_COORD_AXIS.height;
    if (size.width < MIN_COORD_AXIS.width)
      size.width = MIN_COORD_AXIS.width;

    Graphics2D g2 = (Graphics2D) g;
    g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
        RenderingHints.VALUE_ANTIALIAS_ON);
    // Draw coordinate
    g2.setPaint(Color.BLACK);
    final int AXIS_HEIGHT = size.height - TOP_SPACE - BOTTOM_SPACE;
    final int AXIS_WIDTH = size.width - RIGHT_SPACE - LEFT_SPACE;
    // Draw axis Y
    g2.draw(new Line2D.Float(LEFT_SPACE, TOP_SPACE, LEFT_SPACE, AXIS_HEIGHT));
    // Draw axis X
    g2.draw(new Line2D.Float(LEFT_SPACE, AXIS_HEIGHT, AXIS_WIDTH, AXIS_HEIGHT));
    // Draw coordinate arrows
    // Y coordinate arrow
    g2.draw(new Line2D.Float(LEFT_SPACE, TOP_SPACE, LEFT_SPACE
        + ARROW_HALF_WIDTH, TOP_SPACE + ARROW_LENGTH));
    g2.draw(new Line2D.Float(LEFT_SPACE, TOP_SPACE, LEFT_SPACE
        - ARROW_HALF_WIDTH, TOP_SPACE + ARROW_LENGTH));
    // X coordinate arrow
    g2.draw(new Line2D.Float(AXIS_WIDTH, AXIS_HEIGHT,
        AXIS_WIDTH - ARROW_LENGTH, AXIS_HEIGHT + ARROW_HALF_WIDTH));
    g2.draw(new Line2D.Float(AXIS_WIDTH, AXIS_HEIGHT,
        AXIS_WIDTH - ARROW_LENGTH, AXIS_HEIGHT - ARROW_HALF_WIDTH));
    // Draw scale
    // Scale Y
    final int nInternalSpaceY = (AXIS_HEIGHT - ARROW_LENGTH)
        / (PanelCoverage.m_nScaleNumber + 2);
    for (int i = 1; i < PanelCoverage.m_nScaleNumber + 1; i++) {
      int nScalePos = AXIS_HEIGHT - i * nInternalSpaceY;
      if (i % 2 == 0) {
        g2.draw(new Line2D.Float(LEFT_SPACE, nScalePos, LEFT_SPACE
            + SCALE_LARGE_LENGTH, nScalePos));
        g2.drawString(Integer.toString(i / 2 * 10) + "%",
            STRING_Y_AXIS_LEFT_PADDING, nScalePos);
      }
      else
        g2.draw(new Line2D.Float(LEFT_SPACE, nScalePos, LEFT_SPACE
            + SCALE_SHORT_LENGTH, nScalePos));
    }
    // Scale X
    final int nWalkLength = TestExeModel.getWalkLength();

    if (this.m_arrayStages == null)
      computeStages(nWalkLength);

    final int internalSpaceX = (AXIS_WIDTH - ARROW_LENGTH)
        / (PanelCoverage.m_nScaleNumber + 1);
    int[] arrayScaleXPos = new int[m_arrayStages.length];
    int[] arraySScaleYPos = new int[m_arrayStages.length];
    int[] arrayTScaleYPos = new int[m_arrayStages.length];
    int[] arrayTPScaleYPos = new int[m_arrayStages.length];
    int[] arrayAScaleYPos = new int[m_arrayStages.length];
    final int AXIS_Y_LENGTH = AXIS_HEIGHT - TOP_SPACE - ARROW_LENGTH;
    for (int i = 0; i < m_arrayStages.length; i++) {
      int nScaleposY = AXIS_HEIGHT;
      int nScaleposX = LEFT_SPACE + (i + 1) * internalSpaceX;
      if (i % 2 != 0)
        g2.draw(new Line2D.Float(nScaleposX, nScaleposY - SCALE_LARGE_LENGTH,
            nScaleposX, nScaleposY));
      else
        g2.draw(new Line2D.Float(nScaleposX, nScaleposY - SCALE_SHORT_LENGTH,
            nScaleposX, nScaleposY));
      arrayScaleXPos[i] = nScaleposX;
      if (isCoverageDrawable(i)) {
        arraySScaleYPos[i] = (int) ((double) AXIS_HEIGHT - ((double) AXIS_Y_LENGTH
            * m_covS.get(i) / 100.0));
        arrayTScaleYPos[i] = (int) ((double) AXIS_HEIGHT - ((double) AXIS_Y_LENGTH
            * m_covT.get(i) / 100.0));
        arrayTPScaleYPos[i] = (int) ((double) AXIS_HEIGHT - ((double) AXIS_Y_LENGTH
            * m_covTP.get(i) / 100.0));
        arrayAScaleYPos[i] = (int) ((double) AXIS_HEIGHT - ((double) AXIS_Y_LENGTH
            * m_covA.get(i) / 100.0));
      }
      // Draw scale text
      g2.drawString(Integer.toString(m_arrayStages[i]), nScaleposX,
          nScaleposY + 16);
    }
    //System.out.println(isCoverageDrawable(i));
    if (isCoverageDrawable(1)) {
      arraySScaleYPos[0] = arrayTScaleYPos[0] = arrayTPScaleYPos[0] = arrayAScaleYPos[0] = AXIS_HEIGHT;
      arrayScaleXPos[0] = LEFT_SPACE;
      // Draw line chart for state coverage
      boolean[] bShowCoverage = Parameter.getCoverageOption();

      // State coverage
      if (bShowCoverage[0]) {
        g2.setColor(Color.BLACK);
        g2.drawPolyline(arrayScaleXPos, arraySScaleYPos, m_covS.size());
      }
      // Transition coverage
      if (bShowCoverage[1]) {
        g2.setColor(Color.ORANGE);
        g2.drawPolyline(arrayScaleXPos, arrayTScaleYPos, m_covT.size());
      }
      // Transition pair coverage
      if (bShowCoverage[2]) {
        g2.setColor(Color.CYAN);
        g2.drawPolyline(arrayScaleXPos, arrayTPScaleYPos, m_covTP.size());
      }
      // Action coverage
      if (bShowCoverage[3]) {
        g2.setColor(Color.YELLOW);
        g2.drawPolyline(arrayScaleXPos, arrayAScaleYPos, m_covA.size());
      }
    }
  }

  public int[] computeStages(final int nWalkLength)
  {
    int nScaleNum = 0;
    // To set number scales for x coordinate according to random walk length
    double dScaleSpan = 1f;
    if (nWalkLength > m_nScaleNumber) {
      nScaleNum = PanelCoverage.m_nScaleNumber;
      dScaleSpan = (double) nWalkLength / (m_nScaleNumber);
    }
    else
      nScaleNum = nWalkLength;
    m_arrayStages = new int[nScaleNum];
    double j = 0;
    for (int i = 0; i < m_arrayStages.length; i++) {
      j += dScaleSpan;
      m_arrayStages[i] = (int) j;
      // System.out.print(+m_arrayStages[i]+",");
    }
    // System.out.println();
    return m_arrayStages;
  }

  private boolean isCoverageDrawable(int i)
  {
    return (m_covS != null && m_covS.size() > 0 && m_covT != null
        && m_covT.size() > 0 && m_covTP != null && m_covTP.size() > 0
        && m_covA != null && m_covA.size() > 0 && m_covS.size() > i
        && m_covT.size() > i && m_covTP.size() > i && m_covA.size() > i)
        ? true
        : false;
  }

  public void clearCoverages()
  {
    m_covS = new ArrayList<Integer>();
    m_covT = new ArrayList<Integer>();
    m_covTP = new ArrayList<Integer>();
    m_covA = new ArrayList<Integer>();
  }

  public void addStateCoverage(Integer nPercentage)
  {
    m_covS.add(nPercentage);
  }

  public void addTransitionCoverage(Integer nPercentage)
  {
    m_covT.add(nPercentage);
  }

  public void addTransitionPairCoverage(Integer nPercentage)
  {
    m_covTP.add(nPercentage);
  }

  public void addActionCoverage(Integer nPercentage)
  {
    m_covA.add(nPercentage);
  }

  public void redrawGraph()
  {
    this.paintImmediately(0, 0, this.getWidth(), this.getHeight());
    //this.repaint(new Rectangle(LEFT_SPACE, TOP_SPACE, getSize().width-RIGHT_SPACE, getSize().height-BOTTOM_SPACE));
    //this.paintComponent(this.getGraphics());
  }
  
  public void newModel()
  {
    clearCoverages();
    redrawGraph();
  }
}
