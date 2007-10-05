package net.sourceforge.czt.modeljunit.gui;

import java.io.File;

public class FileChooserFilter extends javax.swing.filechooser.FileFilter
{
  private String m_description = null;

  private String m_extension = null;

  public FileChooserFilter(String extension, String description)
  {
    m_description = description;
    m_extension = "." + extension.toLowerCase();
  }

  @Override
  public boolean accept(File f)
  {
    if (f == null)
      return false;
    if (f.isDirectory())
      return true;
    if (f.getName().toLowerCase().endsWith(m_extension))
      return true;
    return false;
  }

  @Override
  public String getDescription()
  {
    return m_description;
  }
}
