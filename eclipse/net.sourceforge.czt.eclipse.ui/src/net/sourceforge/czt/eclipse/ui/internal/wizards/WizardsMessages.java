/**
 * 
 */
package net.sourceforge.czt.eclipse.ui.internal.wizards;

import org.eclipse.osgi.util.NLS;

/**
 * @author Chengdong Xu
 */
public final class WizardsMessages extends NLS
{
  private static final String BUNDLE_NAME = "net.sourceforge.czt.eclipse.ui.internal.wizards.WizardsMessages";//$NON-NLS-1$
  
  private WizardsMessages() {
    // Do not instantiate
  }
  
  /*
   * CZT project creation wizard
   */
  public static String NewCZTProjectWizard_error_title;
  public static String NewCZTProjectWizard_error_create_message;
  public static String NewCZTProjectWizard_initWindowTitle;
  public static String NewCZTProjectWizard_page_title;
  public static String NewCZTProjectWizard_page_description;
  
  public static String NewCZTProjectWizardPage_progressCreating;
  
  /*
   * Z specification creation wizard
   */
  public static String NewZSpecificationWizard_name;
  public static String NewZSpecificationWizard_title;
  public static String NewZSpecificationWizard_description;
  public static String NewZSpecificationWizard_exception_title;
  public static String NewZSpecificationWizard_exception_message;
  public static String NewZSpecificationWizard_windowtitle;
  public static String NewZSpecificationWizardPage_name;
  public static String NewZSpecificationWizardPage_title;
  public static String NewZSpecificationWizardPage_description;
  public static String NewZSpecificationWizardPage_containerLabel;
  public static String NewZSpecificationWizardPage_browseButtonText;
  public static String NewZSpecificationWizardPage_fileLabel;
  public static String NewZSpecificationWizardPage_markupLabel;
  public static String NewZSpecificationWizardPage_markupLaTeX;
  public static String NewZSpecificationWizardPage_markupUTF8;
  public static String NewZSpecificationWizardPage_markupUTF16;
  public static String NewZSpecificationWizardPage_initSpecName;
  public static String NewZSpecificationWizardPage_selectNewFileContainterTitle;
  public static String NewZSpecificationWizardPage_containerMustBeSpecified;
  public static String NewZSpecificationWizardPage_nameMustbeSpecified;
  public static String NewZSpecificationWizardPage_invalidDot;
  public static String NewZSpecificationWizardPage_fileAlreadyExists;
  public static String NewZSpecificationWizardPage_specWizard_progressCreating;
  public static String NewZSpecificationWizardPage_specWizard_specCreating;
  public static String NewZSpecificationWizardPage_specWizard_containerDoesNotExistException;
  public static String NewZSpecificationWizardPage_openingFile;
  
  
  
  

  static {
    NLS.initializeMessages(BUNDLE_NAME, WizardsMessages.class);
  }
}
