package net.sourceforge.czt.ui;

import java.io.File;
import javax.swing.*;
import javax.swing.filechooser.*;

/* ImageFilter.java is used by FileChooserDemo2.java. */
public class CZTFilter extends FileFilter {

    //Accept all directories and all gif, jpg, tiff, or png files.
    public boolean accept(File f) {
        if (f.isDirectory()) {
            return true;
        }

        String extension = Utils.getExtension(f);
        if (extension != null) {
            if (extension.equals(Utils.utf8) ||
                extension.equals(Utils.utf16) ||
                extension.equals(Utils.tex) ||
                extension.equals(Utils.xml) ||
                extension.equals(Utils.zml)) {
                    return true;
            } else {
                return false;
            }
        }

        return false;
    }

    //The description of this filter
    public String getDescription() {
        return "*.utf8,*.utf16,*.tex,*.xml,*.zml";
    }
}

