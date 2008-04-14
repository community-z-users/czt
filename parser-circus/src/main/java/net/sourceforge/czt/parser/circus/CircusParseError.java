/*
 * CircusParseResources.java
 *
 * Created on 22 March 2006, 14:11
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.parser.circus;

import java.util.List;
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
public class CircusParseError
  extends CztErrorImpl
{
  private static String RESOURCE_NAME =
    "net.sourceforge.czt.parser.circus.CircusParseResources";

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
      ParseException parseException = (ParseException)
        sectInfo.get(new Key(source.getName(),
                             ParseException.class));
      List<CztError> errorList = parseException.getErrors();
      CircusParseError error = new CircusParseError(msg, params, locInfo);
      error.setErrorType(errorType);
      error.setInfo(info);
      errorList.add(error);
    }
    catch (CommandException e) {
      e.printStackTrace();
    }
  }
  
  public CircusParseError(CircusParseMessage msg,
                         Object[] params,
                         LocInfo locInfo)
  {
    super(msg.toString(), params, locInfo);
  }

  protected String getResourceName()
  {
    return RESOURCE_NAME;
  }
}
