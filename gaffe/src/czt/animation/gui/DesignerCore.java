package czt.animation.gui;
import czt.animation.gui.design.FormDesign;
class DesignerCore {

  public static int run(String[] args) {
    FormDesign fd=new FormDesign();
    fd.setSize(300,300);
    
    fd.show();
    return 0;
  };
  
};
