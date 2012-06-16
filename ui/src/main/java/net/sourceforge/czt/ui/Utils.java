package net.sourceforge.czt.ui;

import java.io.File;

public class Utils {

    public final static String zed = "zed";
    public final static String zed8 = "zed8";
    public final static String zed16 = "zed16";
    public final static String oz = "oz";
    public final static String oz8 = "oz8";
    public final static String oz16 = "oz16";
    public final static String circus = "circus";
    public final static String circus8 = "circus8";
    public final static String circus16 = "circus16";
    public final static String zedpatt = "zedpatt";
    public final static String zedpatt8 = "zedpatt8";
    public final static String zedpatt16 = "zedpatt16";
    public final static String tex = "tex";
    public final static String zml = "zml";
    public final static String xml = "xml";
    public final static String utf8 = "utf8";
    public final static String utf16 = "utf16";

    /*
     * Get the extension of a file.
     */
    public static String getExtension(File f) {
        String ext = null;
        String s = f.getName();
        int i = s.lastIndexOf('.');

        if (i > 0 &&  i < s.length() - 1) {
            ext = s.substring(i+1).toLowerCase();
        }
        return ext;
    }

  private Utils()
  {
  }
}
