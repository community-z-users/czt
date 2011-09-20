
package net.sourceforge.czt.zeves.response.form;

import java.util.ArrayList;
import java.util.List;

import javax.xml.bind.annotation.XmlAnyElement;
import javax.xml.bind.annotation.XmlAttribute;
import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlEnumValue;
import javax.xml.bind.annotation.XmlRootElement;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.zeves.response.form.ZEvesName.NameClass;

/**
 * <!ELEMENT op (name, (%form;)+, type?)>
 * 
 * @author Andrius Velykis
 *
 */
@XmlRootElement(name = "op")
public class ZEvesOp
{

  /**
   * <!ATTLIST op type (preop | inop | postop) #REQUIRED>
   * 
   * @author Andrius Velykis
   */
  public enum OpType {
    @XmlEnumValue("preop")
    PREOP, 
    @XmlEnumValue("inop")
    INOP, 
    @XmlEnumValue("postop")
    POSTOP
  }

  @XmlAttribute(required = true)
  private OpType type;

  @XmlAttribute(required = true)
  private ZEvesKind kind;

  // name interferes with form here, use #getName()
//  @XmlElement(required = true)
//  private ZEvesName name;

  @XmlElement(name = "type")
  private ZEvesType elType;

  @XmlAnyElement(lax = true)
  private List<?> form = new ArrayList<Object>();

  public ZEvesName getName()
  {
    // always take the first in form
    return (ZEvesName) form.get(0);
  }

  public List<?> getForm()
  {
    // since form interferes with name, it gets caught into the first
    // element here
    return form.subList(1, form.size());
  }

  @Override
  public String toString()
  {

    String opName = fixOpName(String.valueOf(getName()));

    List<?> form = getForm();
    if (form.size() < 1) {
      throw new IllegalStateException("No ZEves Op items: " + form);
    }

    String first = String.valueOf(form.get(0));

    switch (type) {
      case PREOP :
        return opName + " " + first;
      case POSTOP :
        return first + " " + opName;
      case INOP : {
        if (form.size() != 2) {
          throw new IllegalStateException("Invalid ZEves Op items: " + form);
        }
        
        /*
         * A special case for relational image - the LIMG is defined as part of opName,
         * however RIMG is not - need to specify it additionally based on opName class
         */
        String opSuffix = getName().getNameClass() == NameClass.RELIMG ? 
            ZString.SPACE + ZString.RIMG : "";

        return first + " " + opName + " " + String.valueOf(form.get(1)) + opSuffix;
      }
    }

    return "_" + opName + "_";
  }
  
  private String fixOpName(String name) {
    
    String minus = "-";
    if (name.contains(minus)) {
      // Z/Eves for both unary negation and binary minus returns the same character
      // so check and use an appropriate one
      if (type == OpType.PREOP) {
        // unary negation
        return name.replace(minus, ZString.NEG);
      }
      
      if (type == OpType.INOP) {
        // binary minus
        return name.replace(minus, ZString.MINUS);
      }
    }
    
    // nothing to fix
    return name;
  }

}
