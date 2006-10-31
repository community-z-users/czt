
package net.sourceforge.czt.eclipse.editors.parser;

import net.sourceforge.czt.z.ast.ZName;

/**
 * @author Chengdong Xu
 */
public class Triple
{

  private ZName name_;

  private String section_;

  private String type_;

  public Triple(ZName name, String section, String type)
  {
    name_ = name;
    section_ = section;
    type_ = type;
  }

  public ZName getDeclName()
  {
    return name_;
  }

  public void setDeclName(ZName name)
  {
    name_ = name;
  }

  public String getSection()
  {
    return section_;
  }

  public void setSection(String section)
  {
    section_ = section;
  }

  public String getType()
  {
    return type_;
  }

  public void setType(String type)
  {
    type_ = type;
  }

  public String toString()
  {
    return "(" + name_.toString() + ", " + section_ + ", " + type_ + ")";
  }

}
