package net.sourceforge.czt.zeves.response;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;

import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import net.sourceforge.czt.base.util.PerformanceSettings;

@XmlRootElement(name = "zerror")
public class ZEvesError
{
  
  public enum ZEvesErrorType {
    NO_EFFECT,
    PARSE_ERR,
    SCAN_ERR,
    TYPECHECK_ERR,
    UNKNOWN
  }

  private static final String COMMAND_NO_EFFECT_MSG = "Command had no effect.";
  private static final String PARSE_ERR_STR = "[Parser";
  private static final String SCAN_ERR_STR = "[Scanner]";
  private static final String TYPECHECK_ERR_STR = "[Type checker]";

  @XmlElement(name = "errormessage")
  private List<ZEvesErrorMessage> errors = new ArrayList<ZEvesErrorMessage>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

  @Override
  public String toString()
  {
    return ZEvesResponseUtil.concat(errors, "\n");
  }
  
  public List<ZEvesErrorMessage> getMessages() {
    return Collections.unmodifiableList(errors);
  }
  
  public EnumSet<ZEvesErrorType> getType() {
    EnumSet<ZEvesErrorType> errTypes = EnumSet.noneOf(ZEvesErrorType.class);
    
    for (ZEvesErrorMessage err : errors) {
      String message = err.getMessage();
      errTypes.add(getErrorType(message));
    }
    
    return errTypes;
  }
  
  private ZEvesErrorType getErrorType(String message) {
    if (message == null) {
      return ZEvesErrorType.UNKNOWN;
    }
    
    if (COMMAND_NO_EFFECT_MSG.equals(message)) {
      return ZEvesErrorType.NO_EFFECT;
    }
    
    if (message.contains(PARSE_ERR_STR)) {
      return ZEvesErrorType.PARSE_ERR;
    }
    
    if (message.contains(SCAN_ERR_STR)) {
      return ZEvesErrorType.SCAN_ERR;
    }
    
    if (message.contains(TYPECHECK_ERR_STR)) {
      return ZEvesErrorType.TYPECHECK_ERR;
    }
    
    return ZEvesErrorType.UNKNOWN;
  }

}
