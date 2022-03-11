package net.sourceforge.czt.session;

import java.util.Set;

public interface DefaultSectionParents  {

   Dialect getDialect();
   Set<String> defaultParents(String sectName);
}
