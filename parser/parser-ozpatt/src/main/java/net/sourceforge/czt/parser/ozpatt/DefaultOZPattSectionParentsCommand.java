package net.sourceforge.czt.parser.ozpatt;

import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.parser.oz.DefaultOZSectionParentsCommand;

public class DefaultOZPattSectionParentsCommand extends DefaultOZSectionParentsCommand {
	  
	@Override
	public Dialect getDialect() {
		return Dialect.OZPATT;
	}
}
