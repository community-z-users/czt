package net.sourceforge.czt.zeves.response;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlMixed;

public class ZEvesErrorMessage
{

  @XmlMixed
  @XmlAnyElement(lax = true)
  private List<?> content = new ArrayList<Object>();

  @Override
  public String toString()
  {
    return "ERROR: " + getMessage();
  }
  
  public String getMessage() {
    return ZEvesResponseUtil.concat(content, " ");
  }

}
