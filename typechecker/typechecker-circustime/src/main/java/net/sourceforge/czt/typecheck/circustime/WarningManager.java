package net.sourceforge.czt.typecheck.circustime;

import net.sourceforge.czt.session.SectionInfo;

public class WarningManager extends net.sourceforge.czt.typecheck.circus.WarningManager {
		
	  public WarningManager()
	  {
	    super();
	  }

	  /** Creates a new instance of WarningManager
	   * @param forLogger 
	   */
	  public WarningManager(Class<?> forLogger)
	  {
	    super(forLogger);
	  }
	  
	  public WarningManager(SectionInfo manager)
	  {
	    super(manager);
	  }
	  
	  public WarningManager(Class<?> forLogger, SectionInfo manager)
	  {
	    super(forLogger, manager);
	  }

}
