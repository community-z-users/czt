package net.sourceforge.czt.eclipse.ui.internal.preferences;

import java.io.IOException;
import java.net.URL;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.widgets.Display;

/**
 * Loads CZT Sans font from the plug-in if it is not available in the system.
 * 
 * This allows using CZT font within the plug-ins without requiring them to be installed on user's
 * computer.
 * 
 * @author Andrius Velykis
 */
public class CztFontLoad {

  public static String CZT_FONT_NAME = "CZT";

  /**
   * Loads CZT font to be available for SWT widgets, if one does not exists in the system already.
   */
  public static void loadCztFont() {

    Display display = Display.getCurrent();

    // first check if the CZT font already exists in the system
    FontData[] fonts = display.getFontList(CZT_FONT_NAME, true);

    if (fonts.length == 0) {
      loadFont(display, "CZTSans.ttf");
    }
  }

  private static void loadFont(Display display, String fontName) {
    // resolve font URL within the plug-in bundle (note, the font may be inside a JAR here)
    URL fontUrl = CztUIPlugin.getDefault().getBundle().getEntry("fonts/" + fontName);

    if (fontUrl == null) {
      CztUIPlugin.logErrorMessage("Font " + fontName + " cannot be found in the plug-in.");

    } else {
      try {
        URL fontFileUrl = FileLocator.toFileURL(fontUrl);

        // get the file path and try loading the font
        String fontFilePath = new Path(fontFileUrl.getPath()).toOSString();
        boolean loaded = display.loadFont(fontFilePath);

        if (!loaded) {
          CztUIPlugin.logErrorMessage(
              "Font " + fontName + " cannot be loaded from file " + fontFilePath);
        }

      } catch (IOException ex) {
        CztUIPlugin.log("Font " + fontName + " cannot be loaded: " + ex.getMessage(), ex);
      }
    }
  }

}
