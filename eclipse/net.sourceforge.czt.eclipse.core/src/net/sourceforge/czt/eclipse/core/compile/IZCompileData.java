package net.sourceforge.czt.eclipse.core.compile;

import java.util.List;

import org.eclipse.jface.text.Position;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Spec;

/**
 * Represents compilation data for Z specification.
 *  
 * @author Andrius Velykis
 */
public interface IZCompileData
{
  
  public SectionManager getSectionManager();
  
  public Spec getSpec();
  
  public List<? extends CztError> getErrors();

  public Position getTermPosition(Term term);
  
}
