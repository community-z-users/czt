package net.sourceforge.czt.eclipse.ui.internal.outline;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.internal.preferences.PreferenceConstants;
import net.sourceforge.czt.session.Dialect;

/**
 * A factory for visitors that retrieve term labels (e.g. name or description). The returned
 * visitors utilize fallback chain to determine the optimal label. For example, if one "friendly"
 * visitor does not find an appropriate label, the responsibility falls onto a less "friendly"
 * visitor.
 * 
 * The factory supports different visitors for indicated dialects. The current dialect can be
 * passed or is read from preferences.
 * 
 * @author Andrius Velykis
 * @author Leo Freitas
 */
public class TermLabelVisitorFactory
{

  private final static String SHORT_DESCRIPTION_RESOURCE = 
      "net.sourceforge.czt.z.util.ShortDescriptionResourceBundle";

  private final static String ZPATT_SHORT_DESCRIPTION_RESOURCE = 
      "net.sourceforge.czt.zpatt.util.ShortDescriptionResourceBundle";

  private final static String CIRCUS_SHORT_DESCRIPTION_RESOURCE = 
      "net.sourceforge.czt.circus.util.ShortDescriptionResourceBundle";

  private final static String CIRCUSTIME_SHORT_DESCRIPTION_RESOURCE = 
	      "net.sourceforge.czt.circustime.util.ShortDescriptionResourceBundle";

  private final static TermVisitor<String> Z_SHORT_DESC_VISITOR = 
      new net.sourceforge.czt.zpatt.util.ZPattConcreteSyntaxDescriptionVisitor(
      SHORT_DESCRIPTION_RESOURCE, ZPATT_SHORT_DESCRIPTION_RESOURCE);

  private final static TermVisitor<String> CIRCUS_SHORT_DESC_VISITOR = 
      new net.sourceforge.czt.circus.util.CircusConcreteSyntaxDescriptionVisitor(
      SHORT_DESCRIPTION_RESOURCE, CIRCUS_SHORT_DESCRIPTION_RESOURCE);

  private final static TermVisitor<String> CIRCUSTIME_SHORT_DESC_VISITOR = 
	      new net.sourceforge.czt.circustime.util.CircusTimeConcreteSyntaxDescriptionVisitor(
	      SHORT_DESCRIPTION_RESOURCE, CIRCUS_SHORT_DESCRIPTION_RESOURCE, CIRCUSTIME_SHORT_DESCRIPTION_RESOURCE);

  private final static TermVisitor<String> Z_LONG_DESC_VISITOR = 
      new net.sourceforge.czt.zpatt.util.ZPattConcreteSyntaxDescriptionVisitor();

  private final static TermVisitor<String> CIRCUS_LONG_DESC_VISITOR = 
      new net.sourceforge.czt.circus.util.CircusConcreteSyntaxDescriptionVisitor();

  private static TermVisitor<String> createTermVisitor(String dialect, boolean friendly,
      boolean label)
  {
    TermVisitor<String> visitor;
    List<TermVisitor<String>> visitorList = new ArrayList<TermVisitor<String>>();

    if (friendly) {
      visitorList.add(label ? new NodeNameVisitor() : new NodeDescriptionVisitor());
    }

    visitorList.add(label ? getShortDescVisitor(dialect) : getLongDescVisitor(dialect));
    visitorList.add(new TermClassPrintVisitor());

    visitor = new ChainTermVisitor<String>(visitorList);
    return visitor;
  }

  public static TermVisitor<String> getTermLabelVisitor(String dialect, boolean friendly)
  {
    return createTermVisitor(dialect, friendly, true);
  }

  public static TermVisitor<String> getTermLabelVisitor(boolean friendly)
  {
    return getTermLabelVisitor(getDialect(), friendly);
  }

  public static TermVisitor<String> getTermLabelVisitor()
  {
    return getTermLabelVisitor(true);
  }

  public static TermVisitor<String> getTermDescVisitor(String dialect, boolean friendly)
  {
    return createTermVisitor(dialect, friendly, false);
  }

  public static TermVisitor<String> getTermDescVisitor(boolean friendly)
  {
    return getTermDescVisitor(getDialect(), friendly);
  }

  public static TermVisitor<String> getTermDescVisitor()
  {
    return getTermDescVisitor(true);
  }

  private static String getDialect()
  {
    return CztUIPlugin.getDefault().getPreferenceStore().getString(PreferenceConstants.PROP_DIALECT);
  }

  private static TermVisitor<String> getShortDescVisitor(String dialect)
  {

    if (Dialect.CIRCUS.toString().equals(dialect)) {
      return CIRCUS_SHORT_DESC_VISITOR;
    }
    else if (Dialect.CIRCUSTIME.toString().equals(dialect)) {
      return CIRCUSTIME_SHORT_DESC_VISITOR;
    }

    return Z_SHORT_DESC_VISITOR;
  }

  private static TermVisitor<String> getLongDescVisitor(String dialect)
  {

    if ("circus".equals(dialect)) {
      return CIRCUS_LONG_DESC_VISITOR;
    }

    return Z_LONG_DESC_VISITOR;
  }

  private TermLabelVisitorFactory()
  {
  }

}
