package czt.animation.gui.scripting;
import java.awt.Image;
import java.beans.SimpleBeanInfo;

/**
 * Exists for the sole purpose of giving the ScriptDelegateBeanInfo bean an icon.
 */
public class ScriptDelegateBeanInfo extends SimpleBeanInfo {
  public Image getIcon(int iconKind) {
    switch(iconKind) {
     case ICON_COLOR_32x32: case ICON_MONO_32x32:
       return loadImage("ScriptDelegateIcon.gif");
     case ICON_COLOR_16x16: case ICON_MONO_16x16:
       return loadImage("ScriptDelegateIcon.gif")
	 .getScaledInstance(16,16,Image.SCALE_FAST);
     default:
       throw new Error("iconKind should be one of ICON_COLOR_32x32, ICON_MONO_32x32, "
		       +"ICON_COLOR_16x16, ICON_MONO_16x16");
    }     
  };
};
