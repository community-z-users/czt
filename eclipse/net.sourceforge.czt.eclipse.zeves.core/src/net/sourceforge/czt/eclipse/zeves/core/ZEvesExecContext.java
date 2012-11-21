package net.sourceforge.czt.eclipse.zeves.core;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.core.document.IPositionProvider;
import net.sourceforge.czt.text.Position;

/**
 * @author Andrius Velykis
 */
public interface ZEvesExecContext
{

  public enum ZEvesMessageType {
    ERROR,
    WARNING,
    INFO,
    RESULT,
    RESULT_TRUE
  }
  
  public enum ZEvesStatus {
    FINISHED,
    UNFINISHED,
    FAILED,
    UNPROCESSED
  }
  
  public Position adaptFullLine(String file, Position pos);

  public IPositionProvider<? super Term> getTermPositions(String file);
  
  boolean addMessage(String file, Position pos, String message, ZEvesMessageType type);
  
  boolean addStatus(String file, Position pos, ZEvesStatus type);
  
  boolean removeStatus(String file, Position pos, ZEvesStatus type);
  
  boolean clearMarkers(String file);
  
  void completed(String file);
  
}
