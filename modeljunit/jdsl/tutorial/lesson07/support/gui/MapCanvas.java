package support.gui;

import support.AirportSpecs;
import support.FlightSpecs;
import java.util.Enumeration;
import jdsl.core.api.*;
import java.awt.*;
import java.awt.event.*;
import jdsl.graph.api.*;
import java.net.URL;
import java.net.MalformedURLException;

/**
 * Class that displays a map of the USA, draws vertices and edges on it  
 * when asked. 
 *
 * @author Galina Shubina (gs)
 * @version JDSL 2
 */

public class MapCanvas extends Canvas 
  implements MouseListener, MouseMotionListener {
    
    public static final int WIDTH = 642;
    public static final int HEIGHT = 450;
    
    // size of vertices
    public static final int RADIUS = 8;
    public static final int SIDE = 16;
    static final int P_ = 3;
    
    private Color vertex_color = Color.blue; // Standard non-highlighted vertex colour
    private Color edge_color = Color.gray; // Standard non-highlighted edge colour
    private Color hl_color = Color.red; // Colour of edge and vertices highlighted for dragging
    private Color path_color = Color.red;

    private static final String MAP_IMAGE = "support/images/map.gif";

    // rest of the GUI will display messages for us, and wants to know about
    // airport clicks
    private FlightPanel updatePanel_; 
    
    // background_ stores the MAP_IMAGE named above.  It's copied onto
    // the offscreen_ image, and then the vertices and edges are drawn onto
    // offscreen_, and finally offscreen_ is copied onscreen, whenever
    // redrawing is necessary.  Not sure why dep has the offscreen_ level
    // of indirection.
    private Image offImage_;
    private Image background_;
    private Graphics offGraphics_;
    private Dimension offDimension_;
    
    private Graph dataSet_;
    private QueryData queryData_;

    private Label statusLabel_;

    MapCanvas (Graph dataset, QueryData querydata, FlightPanel fpanel, Label statusbar) {
      super();
      
      init(dataset, querydata,fpanel,statusbar);

      //      System.out.println("Application Version");

      background_ = getToolkit().getImage(MAP_IMAGE);

      MediaTracker tracker = new MediaTracker(this);
      try {
	tracker.addImage(background_, 0);
	tracker.waitForID(0);
      } catch(InterruptedException e) { }
      
      offImage_ = createImage(WIDTH,HEIGHT);

    }

    MapCanvas (Graph dataset, QueryData querydata, FlightPanel fpanel, Label statusbar, String docBase) {
      super();

      init(dataset, querydata,fpanel,statusbar);

      //      System.out.println("Applet Version");

      try {
	URL imageSource = new URL(docBase + MAP_IMAGE);

	background_ = getToolkit().getImage(imageSource);

	MediaTracker tracker = new MediaTracker(this);
	try {
	  tracker.addImage(background_, 0);
	  tracker.waitForID(0);
	} catch(InterruptedException e) { }
	
	offImage_ = createImage(WIDTH,HEIGHT);
      } catch (MalformedURLException mure) {
	System.out.println("Cannot load the map");
	offImage_ = createImage(WIDTH,HEIGHT);
      }

    }

    private void init(Graph dataset, QueryData querydata, FlightPanel fpanel, Label statusbar) {
      this.addMouseListener(this); // processes its own mouse clicks
      this.addMouseMotionListener(this); // processes its own mouse movements
      
      dataSet_ = dataset;
      queryData_ = querydata;
      updatePanel_ = fpanel;
      statusLabel_ = statusbar;
    }

    // look through all vertices to see if one's visual representation contains
    // the given point
    synchronized Vertex vertexAt (int x, int y)
    {
        VertexIterator e = dataSet_.vertices();
        while (e.hasNext()) {
            Vertex gvert = e.nextVertex();
	    AirportSpecs gv = (AirportSpecs)gvert.element();
            if (
                    (x >= gv.x() - RADIUS) &&
                    (x <= gv.x() + RADIUS) &&
                    (y >= gv.y() - RADIUS) &&
                    (y <= gv.y() + RADIUS)
		 ) {
	      return gvert;
	    }
        }
        return null;
    }

    // when the mouse is over a vertex, show the vertex's label
    public void mouseMoved (MouseEvent me) {
        Vertex vertex = vertexAt(me.getX(), me.getY());
        if (vertex != null) {
	  if (statusLabel_ != null) {
	    AirportSpecs as = (AirportSpecs)vertex.element();
	    statusLabel_.setText(as.label());
	  }
	}	  
        else {
	  if (statusLabel_ != null) {
	    statusLabel_.setText("");
	  }
	}
    }

    // when an airport is clicked, tell the rest of the world about it
    public void mouseClicked (MouseEvent me) {
        Vertex gv = vertexAt (me.getX(), me.getY());
	if (queryData_.queryPath() != null) {
	  queryData_.setPath(null);
	  queryData_.setFrom(null);
	  queryData_.setTo(null);
	  updatePanel_.updatedQueryData();
	}

        if (gv != null) {
	  if (queryData_.getFrom() != null) {
	    if (queryData_.getTo() != null) {
	      return;
	    } 
	    queryData_.setTo(gv);
	    updatePanel_.updatedQueryData();
	  } else {
	    queryData_.setFrom(gv);
	    updatePanel_.updatedQueryData();
	  }
	}
        // hack hack hack
    }

    // I don't care about any of these events, but I have to "handle" them
    // unless I want to create inner classes
    public void mousePressed (MouseEvent me) { }
    public void mouseReleased (MouseEvent me) { }
    public void mouseEntered (MouseEvent me) { }
    public void mouseExited (MouseEvent me) { }
    public void mouseDragged (MouseEvent me) { }

    private synchronized void drawVertex (AirportSpecs gv, Color c, Graphics g) {
      g.setColor(Color.gray);
      g.fill3DRect(gv.x()-RADIUS, gv.y()-RADIUS,
		   SIDE, SIDE, true);
      g.fill3DRect(gv.x()-RADIUS+1, gv.y()-RADIUS+1,
		   SIDE, SIDE, true);
      g.setColor(c);
      g.fillOval(gv.x()-3, gv.y()-3, 8, 8);
    }
    
    synchronized void drawFlight (FlightSpecs f, AirportSpecs from, AirportSpecs to, Color c, Graphics g, boolean thick) {
      g.setColor(c);
      g.drawLine(from.x(), from.y(), to.x(), to.y());
      if (thick) {
	g.drawLine(from.x()-1, from.y(), to.x()-1, to.y());
	g.drawLine(from.x(), from.y()+1, to.x(), to.y()+1);
      }
    }
    

    public void paint(Graphics g) {
      update(g);
    }

    public void forceUpdate() {
      offGraphics_ = null;
      redraw();
    }

    /*
     * A quick hack so that I wouldn't forget to create and dispose of graphics
     * objects when regenerating the buffer.
     */  
    protected void redraw() {
      Graphics g = getGraphics();
      paint(g);
      g.dispose();
    }


    public void update(Graphics g) {
      Dimension d = getSize();

      if ((offGraphics_ == null)
	  || (d.width != offDimension_.width)
	  || (d.height != offDimension_.height) ) {
        if (offGraphics_ != null)
          offGraphics_.dispose();

        offDimension_ = d;
        offImage_ = createImage(d.width, d.height);
        offGraphics_ = offImage_.getGraphics();
	drawBuffer();        
      }
      
      g.drawImage(offImage_, 0, 0, this);

    }
    
    public void repaint()
    {
      super.repaint();
    }
    
    public void drawBuffer() {
      if (offGraphics_ == null)
        return;
      
      offGraphics_.drawImage(background_,0,0,this);

      EdgeIterator eiter = dataSet_.edges();
      for( ; eiter.hasNext(); ) {
        Edge e = eiter.nextEdge();
        Vertex[] ep = dataSet_.endVertices(e);
        drawFlight((FlightSpecs)e.element(),
		   (AirportSpecs)ep[0].element(),
		   (AirportSpecs)ep[1].element(),
		   edge_color,
		   offGraphics_, false);
      }
      
      EdgeIterator path = queryData_.queryPath();

      Sequence vertexS = new jdsl.core.ref.NodeSequence();
      if (path != null) {
	
	Edge prev_edge = null;
	for( ; path.hasNext(); ) {
	  Edge e = path.nextEdge();
	  Vertex[] ep = dataSet_.endVertices(e);
	  if (prev_edge != null) {
	    vertexS.insertFirst(dataSet_.aCommonVertex(e,prev_edge).element());
	  }
	  drawFlight((FlightSpecs)e.element(),
		     (AirportSpecs)ep[0].element(),
		     (AirportSpecs)ep[1].element(),
		     path_color,
		     offGraphics_, true);
	  prev_edge = e;
	}
	path.reset();
      }


      VertexIterator viter = dataSet_.vertices();
      for( ; viter.hasNext(); ) {
        Vertex v = viter.nextVertex();
        drawVertex((AirportSpecs)v.element(), vertex_color, offGraphics_);
      }
      
      for(ObjectIterator oiter = vertexS.elements(); oiter.hasNext(); ) {
	drawVertex((AirportSpecs)oiter.nextObject(), path_color, offGraphics_);
      }

      Vertex from, to;
      from = queryData_.getFrom();
      to = queryData_.getTo();
      
      // Draw query result if such exists !!!!

      if (from != null) {	
        drawVertex((AirportSpecs)from.element(), hl_color, offGraphics_);
      }

      if (to != null) {
        drawVertex((AirportSpecs)to.element(), hl_color, offGraphics_);
      }

    }



    
}
