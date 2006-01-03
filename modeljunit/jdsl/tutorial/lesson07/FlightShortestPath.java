import support.gui.*;
import support.*;
import java.awt.*;
import java.awt.event.*;
import java.applet.*;

public class FlightShortestPath extends Applet {

  public static final String title_ = "Flights";
  
  /// settings for this Frame, and global settings for all components
  public static final Color APP_BG = Color.lightGray;
  public static final Color APP_FG = Color.black;
  public static final Font  APP_FONT = new Font("Helvetica",Font.PLAIN,11);

  public void init() {
    setLayout(null);
    FlightPanel fp = new FlightPanel(getDocumentBase().toString());
    add(fp);
    
  }

  public static void main(String[] argv) {
    Frame mainFrame;

    mainFrame = new Frame(FlightShortestPath.title_);
    mainFrame.addWindowListener(new WindowAdapter() {
      public void windowClosing (WindowEvent we) {
	System.exit(0);
      }
    });


    Insets insets = mainFrame.getInsets();
      
    mainFrame.setSize(FlightPanel.WIDTH+ insets.left + insets.right,    // Resize twice
		      FlightPanel.HEIGHT + insets.top + insets.bottom);

    mainFrame.setBackground(FlightShortestPath.APP_BG);
    mainFrame.setForeground(FlightShortestPath.APP_FG);
    mainFrame.setResizable(false);
    mainFrame.setLocation(10,50);

    mainFrame.add(new FlightPanel());
    mainFrame.show();
  }

}
