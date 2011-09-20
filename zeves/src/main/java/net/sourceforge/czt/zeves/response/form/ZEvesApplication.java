
package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;

/**
 * <!ELEMENT application (%form;, %form;, type?)>
 * 
 * @author Andrius Velykis
 */
@XmlRootElement(name = "application")
public class ZEvesApplication
{

  @XmlAnyElement(lax = true)
  private List<?> form = new ArrayList<Object>();

  @XmlElement
  private ZEvesType type;

  @Override
  public String toString()
  {

    if (form.size() != 2) {
      throw new IllegalStateException("Invalid ZEvesApplication items: " + form);
    }

    return String.valueOf(form.get(0)) + " " + String.valueOf(form.get(1));
  }

}
