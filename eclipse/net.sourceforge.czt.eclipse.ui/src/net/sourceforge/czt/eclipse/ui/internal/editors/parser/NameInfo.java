
package net.sourceforge.czt.eclipse.ui.internal.editors.parser;

import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.PrintVisitor;

/**
 * @author Chengdong Xu
 */
public class NameInfo
{

  private ZName name_;

  private String section_;

  private String type_;
  
  private boolean isLocal_;
  
  private static final class LazyPVLoader {
	  private static final PrintVisitor INSTANCE = new PrintVisitor();
  }

  public NameInfo(ZName name, String section, String type, boolean isLocal)
  {
    name_ = name;
    section_ = section;
    type_ = type;
    isLocal_ = isLocal;
  }

  public ZName getName()
  {
    return name_;
  }

  public void setName(ZName name)
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
  
  /**
   * @unused
   * @return
   */
  public boolean isLocal()
  {
    return isLocal_;
  }
  
  /**
   * @unused
   * @param isLocal
   */
  public void setLocal(boolean isLocal)
  {
    isLocal_ = isLocal;
  }

  public String toString()
  {
    return "(" + name_.accept(LazyPVLoader.INSTANCE) + ", " + section_ + ", " + type_ + ")";
  }

}
