package czt.animation.gui;
import java.beans.beancontext.*;
import czt.animation.gui.history.History;
import czt.animation.gui.history.BasicHistory;
/**
 * The base for AnimatorCore and AnimatorScrollingCore
 */
abstract class AnimatorCoreBase implements BeanContextProxy {
  //Properties:
  /**
   * History property.
   * Keeps track of history of solution sets.
   */
  protected History history;
  /**
   * Getter function for {@link #history history}.
   * @return The property <code>history</code>.
   * @see #history
   */
  public History    getHistory()                  {return history;};
  /**
   * Setter function for {@link #history history}.
   * @param h The property <code>history</code>.
   * @see #history
   */
  public void       setHistory(History h)         {history=h;};
  
  /**
   * Mode property.
   * True if in animate mode, false if in design mode.
   */
  protected boolean animateMode;
  /**
   * Getter function for {@link #animateMode animateMode}.
   * @return The property <code>animateMode</code>.
   * @see #animateMode
   */
  public boolean    isAnimateMode()               {return animateMode;};
  /**
   * Getter function for {@link #animateMode animateMode}.
   * @return The property <code>animateMode</code>.
   * @see #animateMode
   */
  public boolean    getAnimateMode()              {return animateMode;};
  /**
   * Setter function for {@link #animateMode animateMode}.
   * @param m The property <code>animateMode</code>.
   * @see #animateMode
   */
  public void       setAnimateMode(boolean m)     {animateMode=m;}

  //BeanContextProxy stuff
  /**
   * The Bean context for this object (proxied through 
   * {@link #getBeanContextProxy() #getBeanContextProxy()}).
   * Provides services to contexts and beans in the program.
   */
  protected BeanContextServices    rootContext;
  /**
   * Getter function for {@link #rootContext rootContext}.
   * @return The root context.
   * @see #rootContext
   * @see java.beans.beancontext.BeanContextProxy
   */
  public BeanContextChild getBeanContextProxy() {return rootContext;};
  
  //Constructors
  /**
   * Default constructor.
   * Sets history to be a {@link czt.animation.gui.history.BasicHistory BasicHistory}.
   * Sets to design mode.
   * Initialises empty context.
   * @see czt.animation.gui.history.BasicHistory
   */
  protected AnimatorCoreBase() {
    history=new BasicHistory();
    animateMode=false;
    rootContext=new BeanContextServicesSupport();
  };

  /**
   * Constructor.
   * Allows subclasses to override the defaults for {@link #history history}, 
   * {@link #animateMode animateMode}, and {@link #rootContext rootContext}.
   * @param h history
   * @param am animateMode
   * @param rc rootContext
   */
  protected AnimatorCoreBase(History h, boolean am, BeanContextServices rc) {
    history=h; 
    animateMode=am;
    rootContext=rc;
  };

  public static int run(String[] args) {
    return 0;//XXX
  };
  
};
