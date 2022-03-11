package net.sourceforge.czt.ui;

import java.io.File;
import javax.swing.filechooser.*;

/* ImageFilter.java is used by FileChooserDemo2.java. */
public class CZTFilter extends FileFilter {

    //Accept all directories and all CZT-related files.
    public boolean accept(File f) {
        if (f.isDirectory()) {
            return true;
        }

        String extension = Utils.getExtension(f);
        if (extension != null) {
            if (
                extension.equals(Utils.zed) ||
                extension.equals(Utils.zed8) ||
                extension.equals(Utils.zed16) ||
                extension.equals(Utils.oz) ||
                extension.equals(Utils.oz8) ||
                extension.equals(Utils.oz16) ||
                extension.equals(Utils.circus) ||
                extension.equals(Utils.circus8) ||
                extension.equals(Utils.circus16) ||
                extension.equals(Utils.zedpatt) ||
                extension.equals(Utils.zedpatt8) ||
                extension.equals(Utils.zedpatt16) ||
                extension.equals(Utils.utf8) ||
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
        return "Common CZT files *.zed*,*.oz*,*.circus*,*.zedpatt*,*.utf8,*.utf16,*.tex,*.xml,*.zml";
    }
}

