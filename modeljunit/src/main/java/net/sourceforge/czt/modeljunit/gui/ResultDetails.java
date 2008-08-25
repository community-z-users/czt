
package net.sourceforge.czt.modeljunit.gui;

/*
 * @author rong 30th/July/2007
 */

public class ResultDetails
{
  String strType; // Waring,Error

  String strName; // Exception name

  String strDescription; // Result description

  String strLocation; // Column number and line number

  String strPath; // The path of the file and file name

  public ResultDetails(String type, String name, String desc, String location,
      String path)
  {
    strType = type;
    strName = name;
    strDescription = desc;
    strLocation = location;
    strPath = path;
  }
}
