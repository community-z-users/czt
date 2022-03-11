package net.sourceforge.czt.parser.z;

import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.parser.util.LocInfo;
import net.sourceforge.czt.parser.util.LocInfoImpl;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * A dynamic error to report parent cycles. If we capture the warnings about
 * cyclic parent relationships at the level of LatexMarkupParser, it means
 * that the related ZSects have already been parsed and added to the SectionInfo.
 * Therefore InfoTable calls will resolve these sections and would not report
 * another cycle.
 * 
 * Basically, we need to report the warnings about cycles (just as in the Parser
 * for InfoTables) here. However, at the level of LatexMarkupParser we do not
 * have locations of the parents (just their names) to correctly report the
 * warnings in the UI. For that reason, this error defers resolution of parent
 * location. If it is queried for the location after completion of parsing, it
 * will try resolving the correct parent location from the parsed objects in
 * the SectionInfo.
 * 
 * @author Andrius Velykis
 */
public class CyclicParentError extends ZParseError
{ 
  private final SectionInfo sectInfo;
  
  private final Key<ZSect> sectKey;
  
  private final String parentName;
  // parent index is used if there is more than one parent
  private final int parentIndex;
  private final String source;
  
  private LocInfo parentLoc = null;
  
  public CyclicParentError(SectionInfo sectInfo, String sectName, String parentName,
      int parentIndex, String source, String cycleStr)
  {  
    // init with null location - it will be resolved dynamically
    super(sectInfo, ZParseMessage.MSG_CYCLIC_PARENT, new String[] {cycleStr}, null);
    setErrorType(ErrorType.WARNING);
    if (sectInfo == null) throw new NullPointerException();
    this.sectInfo = sectInfo;
    
    this.sectKey = new Key<ZSect>(sectName, ZSect.class);
    this.parentName = parentName;
    this.parentIndex = parentIndex;
    
    this.source = source;
  }
  
  private LocInfo getLoc() {
    
    if (parentLoc != null) {
      // already found - use that
      return parentLoc;
    }
    
    // Check if the section has already been parsed, and then try and find
    // the parent location.
    if (sectInfo.isCached(sectKey)) {
      // avoid parsing - only check if the section has been parsed already
      try {
        ZSect sect = sectInfo.get(sectKey);
        int parentCount = -1;
        for (Parent parent : sect.getParent()) {
          if (parentName.equals(parent.getWord())) {
            parentCount++;
            if (parentCount == parentIndex) {
              // found the parent!
              parentLoc = new LocInfoImpl(sectInfo.getDialect(), parent.getAnn(LocAnn.class));
              return parentLoc;
            }
          }
        }
      } catch (CommandException ce) {
        // should never happen, section already cached
        throw new CztException(ce);
      }
    }
    
    // cannot find the parent - return a dummy location
    return new LocInfoImpl(sectInfo.getDialect(), source, 0, 0);
  }

  @Override
  public int getLine()
  {
    return getLoc().getLine();
  }

  @Override
  public int getColumn()
  {
    return getLoc().getColumn();
  }

  @Override
  public int getStart()
  {
    return getLoc().getStart();
  }

  @Override
  public int getLength()
  {
    return getLoc().getLength();
  }

  @Override
  public String getSource()
  {
    return getLoc().getSource();
  }
  
  /**
   * Reports the parent cyclic error to the central ParseException.
   * The special {@link CyclicParentError} is used to allow for dynamic location resolution,
   * e.g. when location cannot be calculated immediately.
   * 
   * @param sectInfo
   * @param source
   * @param sectName
   * @param parentName
   * @param parentIndex
   * @param cycleStr
   */
  public static void reportCyclicParentNoLoc(SectionInfo sectInfo, Source source, String sectName,
      String parentName, int parentIndex, String cycleStr)
  {
    CyclicParentError error = new CyclicParentError(sectInfo, sectName, 
        parentName, parentIndex, source.getName(), cycleStr);
    report(source, error);
  }
  
  public static void reportCyclicParent(SectionInfo sectInfo, Source source, String cycleStr,
      LocInfo location)
  {
    report(sectInfo,
        source,
        ErrorType.WARNING,
        ZParseMessage.MSG_CYCLIC_PARENT,
        new String[] { cycleStr },
        location);
  }
  
}
