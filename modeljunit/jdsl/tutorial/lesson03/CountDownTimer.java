import java.util.*;
import java.awt.*;
import java.awt.geom.*;
import jdsl.core.api.*;
import jdsl.core.ref.*;

/**
	* @author Robert Cohen (rfc)
	* @version JDSL 2
	*/
public class CountDownTimer extends Canvas implements Runnable {
  
  Thread projector;
  long delay=1000;       //one second
  int time, timeLeft;
  int xPos;
  int yPos;
  boolean initialized;
  Sequence listeners = new ArraySequence();
  boolean running;
  
  public CountDownTimer(int secs) {
    delay = 1000; // once a second
    timeLeft = secs;
    time=secs;
    setFont( new Font( "Arial", Font.BOLD + Font.ITALIC, 36 ) );
  }/* init */
  
  public void start() {
    if( projector == null )
      projector = new Thread( this, "CountDownTimer" );
    running=true;
    projector.start();
  }/* start */
  
  public void run() {
    while(running&&(Thread.currentThread()==projector)&&(timeLeft>0)) {
      try { Thread.sleep( delay ); 
      }
      catch( InterruptedException e ) {}
      if (!running) {break;}
      timeLeft--;
      notifyListeners();
      repaint();
    }
  }
  
  public boolean isRunning() {
    if (projector==null)
      return false;
    else
      return projector.isAlive();
  }
  
  
  public void paint( Graphics g ) {
    if (!initialized) {
      setPos();
      initialized=true;
    }    
    g.drawString(String.valueOf(timeLeft),xPos,yPos);
  }/* update */
  
  public void stop() {
    running = false;
    projector=null;
  }/* stop */
  
  public void reset() {
    stop();
    timeLeft=time;
    repaint();
  }
  
  public void addCountDownTimerListener(CountDownTimerListener c) {
    listeners.insertLast(c);
  }
  
  public void notifyListeners() {
    CountDownTimerEvent e = new CountDownTimerEvent(this, timeLeft);
    for(ObjectIterator i=listeners.elements();i.hasNext();)
      ((CountDownTimerListener)i.nextObject()).timerTicked(e);
  }
  
  private void setPos() {
    Graphics g = getGraphics();
    FontMetrics fm=g.getFontMetrics();
    String str=String.valueOf(timeLeft);
    Rectangle2D bounds = fm.getStringBounds(str,g);
    int textWidth = (int)bounds.getWidth();
    int textHeight = (int)bounds.getHeight();
    Dimension canvasSize = getSize();
    int canvasHeight=canvasSize.height;
    int canvasWidth=canvasSize.width;
    xPos = (canvasWidth<textWidth) ? 0 : (canvasWidth-textWidth)/2;
    yPos = (canvasHeight<textHeight) ? 0 : 
      (canvasHeight-textHeight)/2 + textHeight;
  }
}
