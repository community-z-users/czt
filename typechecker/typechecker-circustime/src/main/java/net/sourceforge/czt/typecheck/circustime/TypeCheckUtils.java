/*
  Copyright (C) 2006, 2007 Leo Freitas
  This file is part of the czt project.
 
  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.
 
  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
 
  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.typecheck.circustime;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus.impl.CircusFactoryImpl;
import net.sourceforge.czt.circustime.ast.CircusTimeFactory;
import net.sourceforge.czt.circustime.impl.CircusTimeFactoryImpl;
import net.sourceforge.czt.parser.circus.WarningManager;
import net.sourceforge.czt.parser.circustime.ParseUtils;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.typecheck.circustime.impl.Factory;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.impl.ZFactoryImpl;


public class TypeCheckUtils 
    extends net.sourceforge.czt.typecheck.circus.TypeCheckUtils {
  
  private static final TypeCheckUtils instance_ = new TypeCheckUtils();
 /**
   * Do not generate instances of this class.
   * You should use the static methods directly.
   */
  protected TypeCheckUtils()
  {
    super();
  }
    
  @Override
  protected List<net.sourceforge.czt.typecheck.z.ErrorAnn> lTypecheck(Term term,
                                                SectionManager sectInfo,
                                                boolean recursiveTypes,
                                                boolean sortDeclNames,
                                                boolean useNameIds,
                                                WarningManager.WarningOutput warningOutput,
                                                String sectName)
  {
	ZFactory zFactory = new ZFactoryImpl();
	CircusFactory circusFactory = new CircusFactoryImpl();
    CircusTimeFactory circustimeFactory = new CircusTimeFactoryImpl();    
    Factory factory = new Factory(zFactory, circusFactory, circustimeFactory);
    TypeChecker typeChecker = new TypeChecker(factory,sectInfo, recursiveTypes, sortDeclNames);
    typeChecker.setPreamble(sectName, sectInfo);
    typeChecker.setUseNameIds(useNameIds);
    typeChecker.getWarningManager().setWarningOutput(warningOutput);    
    List<net.sourceforge.czt.typecheck.z.ErrorAnn> errors = new ArrayList<net.sourceforge.czt.typecheck.z.ErrorAnn>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
    errors.addAll(guardedTypeCheck(typeChecker, term));
    for(net.sourceforge.czt.typecheck.z.ErrorAnn err : typeChecker.getWarningManager().warnErrors())
    {
      errors.add(err);
    }
    return errors;    
  }
  
  protected Term parse(Source source, SectionManager sectInfo)
    throws IOException, net.sourceforge.czt.parser.util.ParseException,
      net.sourceforge.czt.base.util.UnmarshalException
  {
    return ParseUtils.parse(source, sectInfo);
  }  
   
  public static void main(String[] args)
    throws IOException, net.sourceforge.czt.base.util.UnmarshalException
  {    
    instance_.run(args);
  }
    
}
