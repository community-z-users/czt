package czt.animation.gui;

import com.ibm.bsf.BSFManager;

import czt.animation.gui.history.History;
import czt.animation.gui.scripting.BSFServiceProvider;

/**
 * The core program for normal animation of a specification.
 */
abstract class AnimatorCore extends AnimatorCoreBase {
  /**
   * Creates an AnimatorCore.
   */
  public AnimatorCore() {
    BSFManager bsfm=new BSFManager();
    //XXX (register any new scripting languages)
    //XXX register and declare beans in bsfm
    rootContext.addService(BSFManager.class,new BSFServiceProvider(bsfm));
    
    //XXX load interface file somewhere...

    //XXX activate initialisation schema.
  };
  
  
};
