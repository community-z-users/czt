package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.Iterator;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.impl.*;

/**
 */
class SpecChecker
  extends Checker
  implements SpecVisitor,
             ZSectVisitor,
             ParentVisitor,
             SectVisitor
{
  public SpecChecker(CheckerInfo info)
  {
    super(info);
  }

  public Object visitSpec(Spec spec)
  {
    List sects = spec.getSect();
    for (Iterator iter = sects.iterator(); iter.hasNext(); ) {
      Sect sect = (Sect) iter.next();
      sect.accept(this);

      //annotate this section with the type info from this section
      //and its parents
      addAnn(sect, sectTypeEnv().getSectTypeEnvAnn());
    }

    //sectTypeEnv().dump();

    //if there are any errors, return false
    Boolean result = Boolean.TRUE;
    if (errors().size() > 0) {
      result = Boolean.FALSE;
    }
    return result;
  }

  /**
   * Any "left over" sections.
   */
  public Object visitSect(Sect sect)
  {
    return Boolean.TRUE;
  }

  public Object visitZSect(ZSect zSect)
  {
    debug("visiting ZSect " + zSect.getName());

    sectName(zSect.getName());

    //if this section has already been declared, raise an error
    if (sectTypeEnv().isChecked(sectName())) {
      ErrorAnn message = errorFactory().redeclaredSection(zSect);
      error(zSect, message);
    }

    //set this as the new section in SectTypeEnv and ErrorFactory
    sectTypeEnv().setSection(sectName());
    errorFactory().setSection(sectName());

    //get and visit the parent sections of the current section
    List parents = zSect.getParent();
    List names = list();
    for (Iterator iter = parents.iterator(); iter.hasNext(); ) {
      Parent parent = (Parent) iter.next();
      parent.accept(this);

      if (names.contains(parent.getWord())) {
        ErrorAnn message = errorFactory().redeclaredParent(parent, sectName());
        error(parent, message);
      }
      else if (parent.getWord().equals(sectName())) {
        ErrorAnn message = errorFactory().selfParent(parent);
        error(parent, message);
      }
      else {
        names.add(parent.getWord());
      }
    }

    //get and visit the paragraphs of the current section
    List paras = zSect.getPara();
    for (Iterator iter = paras.iterator(); iter.hasNext(); ) {
      Para para = (Para) iter.next();
      para.accept(paraChecker());
    }

    //post-check any previously unresolved expressions
    postChecker().postCheck();

    //print any errors
    for (Iterator iter = errors().iterator(); iter.hasNext(); ) {
      Object next = iter.next();
      logger().warning(next.toString() + "\n");
    }

    //if there are any errors, return false
    Boolean result = Boolean.TRUE;
    if (errors().size() > 0) {
      result = Boolean.FALSE;
    }
    return result;
  }

  public Object visitParent(Parent parent)
  {
    sectTypeEnv().addParent(parent.getWord());

    //get the types of the parent... this should be updated once the
    //session manager is finalised
    if (!sectTypeEnv().isChecked(parent.getWord())) {
      Term term = (Term) sectInfo().getInfo(parent.getWord(), ZSect.class);
      String section = sectTypeEnv().getSection();
      TypeCheckUtils.typecheck(term, sectInfo(), sectTypeEnv());
      sectTypeEnv().setSection(section);
      errorFactory().setSection(section);
    }
    return null;
  }
}
