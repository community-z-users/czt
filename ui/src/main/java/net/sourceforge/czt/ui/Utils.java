package net.sourceforge.czt.ui;

import java.io.File;

public class Utils {

    public final static String utf8 = "utf8";
    public final static String utf16 = "utf16";
    public final static String tex = "tex";
    public final static String xml = "xml";
    public final static String zml = "zml";

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
}
