/*
 * ZSideKickPlugin.java
 * Copyright (C) 2006, 2007 Petra Malik
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */
package net.sourceforge.czt.jedit.zsidekick;

import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.util.WarningManager;
import org.gjt.sp.jedit.EditPlugin;
import org.gjt.sp.jedit.jEdit;

public class ZSideKickPlugin
  extends EditPlugin implements net.sourceforge.czt.parser.util.ParsePropertiesKeys,
                                net.sourceforge.czt.print.util.PrintPropertiesKeys,
                    	          net.sourceforge.czt.typecheck.z.TypecheckPropertiesKeys,
                                net.sourceforge.czt.typecheck.oz.TypecheckPropertiesKeys,
                                net.sourceforge.czt.vcg.z.dc.DomainCheckPropertyKeys,
                                net.sourceforge.czt.vcg.z.feasibility.FeasibilityPropertyKeys
{
  // parser
  //    ignore_unknown_latex_commands
  
  // printer
  //    print_name_ids
  //    print_z_eves
  //    txt_width

  // Typechecking Z
  //    typecheck_debug
  //    typecheck_use_before_decl
  //    typecheck_recursive_types
  //    typecheck_sort_decl_names
  //    typecheck_use_nameids
  //    typecheck_raise_warnings
  //    typecheck_use_spec_reader
  
  // Typechecking OZ related
  //    typecheck_use_strong_typing

  // VCG related
  //    vcg_process_parents
  //    vcg_add_trivial_vc
  //    vcg_parents_to_ignore
  //    vcg_apply_transformers
  //    vcg_raise_type_warnings
  //    vcgu_preferred_markup
  // DC VCG
  //    vcg_dc_use_infix_appliesto
  // FSB VCG
  //    vcg_fsb_add_givenset_vcs
  //    vcg_fsb_create_zschemas

  // jEdit related
  public static final String DEBUG_LOG_FILENAME=
    "JEdit-SectionManager.log";


  public static final String PROP_SHOW_COMPLETE_TREE =
          "show_complete_tree";

  public static final String PROPERTY_PREFIX = "net.sourceforge.czt.jedit.zsidekick.";
  public static final String OPTION_PREFIX = "options." + PROPERTY_PREFIX;
  
  // CZT Session related
  public static final String PROP_CZTPATH = "czt.path";

  public static final String PROP_RESET_SM = "reset_sm";

  public static boolean debug_ = false;

  // some of the "dead code" below is due to conditional values of default constants 
  // from other projects. If they change, the dead code is revived! 
@SuppressWarnings("unused")
public static void setDefaultProperties()
  {
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS,
            ZSideKickPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS_DEFAULT);

    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_SHOW_COMPLETE_TREE, false);

    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_PRINT_NAME_IDS,
              ZSideKickPlugin.PROP_PRINT_NAME_IDS_DEFAULT);

    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_PRINT_ZEVES,
              ZSideKickPlugin.PROP_PRINT_ZEVES_DEFAULT);

    if(ZSideKickPlugin.PROP_TXT_WIDTH_DEFAULT > 0)
			jEdit.setProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TXT_WIDTH, 
              String.valueOf(ZSideKickPlugin.PROP_TXT_WIDTH_DEFAULT));
		else
			jEdit.unsetProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TXT_WIDTH);

    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_USE_BEFORE_DECL,
              ZSideKickPlugin.PROP_TYPECHECK_USE_BEFORE_DECL_DEFAULT);

    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_WARNINGS_OUTPUT,
              ZSideKickPlugin.PROP_TYPECHECK_WARNINGS_OUTPUT_DEFAULT.equals(WarningManager.WarningOutput.RAISE));

    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_RECURSIVE_TYPES,
              ZSideKickPlugin.PROP_TYPECHECK_RECURSIVE_TYPES_DEFAULT);

    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_TYPECHECK_USE_STRONG_TYPING,
            ZSideKickPlugin.PROP_TYPECHECK_USE_STRONG_TYPING_DEFAULT);

    // for shared properties, all or nothing
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_PROCESS_PARENTS,
            ZSideKickPlugin.PROP_VCG_DOMAINCHECK_PROCESS_PARENTS_DEFAULT &&
            ZSideKickPlugin.PROP_VCG_FEASIBILITY_PROCESS_PARENTS_DEFAULT);

    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_ADD_TRIVIAL_VC,
            ZSideKickPlugin.PROP_VCG_DOMAINCHECK_ADD_TRIVIAL_VC_DEFAULT &&
            ZSideKickPlugin.PROP_VCG_FEASIBILITY_ADD_TRIVIAL_VC_DEFAULT);

    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_APPLY_TRANSFORMERS,
            ZSideKickPlugin.PROP_VCG_DOMAINCHECK_APPLY_TRANSFORMERS_DEFAULT &&
            ZSideKickPlugin.PROP_VCG_FEASIBILITY_APPLY_TRANSFORMERS_DEFAULT);

    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO,
            ZSideKickPlugin.PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO_DEFAULT);

    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_FEASIBILITY_ADD_GIVENSET_VCS,
            ZSideKickPlugin.PROP_VCG_FEASIBILITY_ADD_GIVENSET_VCS_DEFAULT);

    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS,
            ZSideKickPlugin.PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS_DEFAULT);

    jEdit.setBooleanProperty("net.sourceforge.czt.jedit.zsidekick.debugZsideKick", false);

    jEdit.setProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_CZTPATH, "");
  }

  public static void resetSM()
  {
    jEdit.setBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_RESET_SM, true);
  }

  public static void setProperties(SectionManager manager)
  {
    boolean value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS);
    manager.setProperty(ZSideKickPlugin.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS, String.valueOf(value));

    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_PRINT_NAME_IDS);
    manager.setProperty(ZSideKickPlugin.PROP_PRINT_NAME_IDS, String.valueOf(value));

    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_PRINT_ZEVES);
    manager.setProperty(ZSideKickPlugin.PROP_PRINT_ZEVES, String.valueOf(value));

    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_USE_BEFORE_DECL);
    manager.setProperty(ZSideKickPlugin.PROP_TYPECHECK_USE_BEFORE_DECL, String.valueOf(value));

    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_WARNINGS_OUTPUT);
    manager.setProperty(ZSideKickPlugin.PROP_TYPECHECK_WARNINGS_OUTPUT, String.valueOf(value ?
        WarningManager.WarningOutput.RAISE : WarningManager.WarningOutput.SHOW));
    // use one setting only for raise type warnings ?
    manager.setProperty(ZSideKickPlugin.PROP_VCG_RAISE_TYPE_WARNINGS, String.valueOf(value));

    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
              ZSideKickPlugin.PROP_TYPECHECK_RECURSIVE_TYPES);
    manager.setProperty(ZSideKickPlugin.PROP_TYPECHECK_RECURSIVE_TYPES, String.valueOf(value));

    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_TYPECHECK_USE_STRONG_TYPING);
    manager.setProperty(ZSideKickPlugin.PROP_TYPECHECK_USE_STRONG_TYPING, String.valueOf(value));

    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_PROCESS_PARENTS);
    manager.setProperty(ZSideKickPlugin.PROP_VCG_PROCESS_PARENTS, String.valueOf(value));

    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_ADD_TRIVIAL_VC);
    manager.setProperty(ZSideKickPlugin.PROP_VCG_ADD_TRIVIAL_VC, String.valueOf(value));

    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_APPLY_TRANSFORMERS);
    manager.setProperty(ZSideKickPlugin.PROP_VCG_APPLY_TRANSFORMERS, String.valueOf(value));

    value = jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO);
    manager.setProperty(ZSideKickPlugin.PROP_VCG_DOMAINCHECK_USE_INFIX_APPLIESTO, String.valueOf(value));

    value = jEdit.getBooleanProperty("net.sourceforge.czt.jedit.zsidekick.debugZsideKick");
    debug_ = value;
    manager.setTracing(value);

    //int width = buffer.getIntegerProperty(propname, 0); TODO: buffer or jEdit?
    int width = jEdit.getIntegerProperty(ZSideKickPlugin.PROPERTY_PREFIX +
                                         ZSideKickPlugin.PROP_TXT_WIDTH, 80);
    if (width > 0)
    {
      manager.setProperty(ZSideKickPlugin.PROP_TXT_WIDTH, String.valueOf(width));
    }

    String cztPath = jEdit.getProperty(ZSideKickPlugin.PROPERTY_PREFIX +
            ZSideKickPlugin.PROP_CZTPATH);
    if (cztPath != null)
    {
      manager.setProperty(ZSideKickPlugin.PROP_CZTPATH, cztPath);
    }
  }

  @Override
  public void start()
  {
    setDefaultProperties();
  }
}
