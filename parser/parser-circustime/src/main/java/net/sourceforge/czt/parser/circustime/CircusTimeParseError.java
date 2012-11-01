/*
 * CircusParseResources.java
 *
 * Created on 22 March 2006, 14:11
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.parser.circustime;

import java.util.List;
import java.util.ResourceBundle;

import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.LocInfo;
import net.sourceforge.czt.parser.util.CztErrorImpl;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.Source;

/**
 * A parse error.
 */
public class CircusTimeParseError
  extends CztErrorImpl
{
  private static String RESOURCE_NAME =
    "net.sourceforge.czt.parser.circustime.CircusParseResources";

  public static void report(SectionInfo sectInfo,
                            Source source,
                            ErrorType errorType,
                            CircusParseMessage msg,
                            Object[] params,
                            LocInfo locInfo)
  {
    report(sectInfo, source, errorType, msg, params, locInfo, null);
  }

  public static void report(SectionInfo sectInfo,
                            Source source,
                            ErrorType errorType,
                            CircusParseMessage msg,
                            Object[] params,
                            LocInfo locInfo,
                            String info)
  {
    try {
      ParseException parseException = 
        sectInfo.get(new Key<ParseException>(source.getName(),
                             ParseException.class));
      List<CztError> errorList = parseException.getErrors();
      CircusTimeParseError error = new CircusTimeParseError(msg, params, locInfo);
      error.setErrorType(errorType);
      error.setInfo(info);
      errorList.add(error);
    }
    catch (CommandException e) {
      e.printStackTrace();
    }
  }
  
  public CircusTimeParseError(CircusParseMessage msg,
                         Object[] params,
                         LocInfo locInfo)
  {
    super(msg.toString(), params, locInfo);
  }

  @Override
  protected ResourceBundle getResourceBundle()
  {
    return ResourceBundle.getBundle(RESOURCE_NAME);
  }
}
