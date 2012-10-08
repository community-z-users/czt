package net.sourceforge.czt.eclipse.ui.internal.editors;


import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.graphics.Font;

/**
 * Handles editor font changes for source viewers.
 * 
 * @author Chengdong Xu
 * @author Andrius Velykis
 */
public class FontUpdater
{
  
  private final ISourceViewer viewer;
  private String fontKey;

  /**
   * Creates a source updater for the given viewer, configuration and preference store.
   *
   * @param viewer the viewer
   * @param configuration the configuration
   * @param preferenceStore the preference store
   * @param fontDefinitionKey font to which changes to listen
   */
  protected FontUpdater(final ISourceViewer viewer, 
      final ZSourceViewerConfiguration configuration,
      final IPreferenceStore preferenceStore, 
      String fontDefinitionKey)
  {
    this.viewer = viewer;
    this.fontKey = fontDefinitionKey;
    Assert.isNotNull(viewer);
    Assert.isNotNull(configuration);
    Assert.isNotNull(preferenceStore);
    
    final IPropertyChangeListener fontChangeListener = new IPropertyChangeListener()
    {
      @Override
      public void propertyChange(PropertyChangeEvent event)
      {
        if (event.getProperty().equals(fontKey)) {
          setControlFont(viewer, fontKey);
        }
      }
    };
    
    final IPropertyChangeListener propertyChangeListener = new IPropertyChangeListener()
    {
      @Override
      public void propertyChange(PropertyChangeEvent event)
      {
        if (configuration.affectsTextPresentation(event)) {
          configuration.handlePropertyChangeEvent(event);
          viewer.invalidateTextPresentation();
        }
      }
    };
    
    viewer.getTextWidget().addDisposeListener(new DisposeListener()
    {
      @Override
      public void widgetDisposed(DisposeEvent e)
      {
        preferenceStore.removePropertyChangeListener(propertyChangeListener);
        JFaceResources.getFontRegistry().removeListener(fontChangeListener);
      }
    });
    
    JFaceResources.getFontRegistry().addListener(fontChangeListener);
    preferenceStore.addPropertyChangeListener(propertyChangeListener);
  }
  
  private static void setControlFont(ISourceViewer viewer, String fontKey) {
    Font font = JFaceResources.getFont(fontKey);
    viewer.getTextWidget().setFont(font);
  }

  public void setFont(String fontKey) {
    this.fontKey = fontKey;
    setControlFont(viewer, fontKey);
  }
  
  public static FontUpdater enableFor(final ISourceViewer viewer, 
      final ZSourceViewerConfiguration configuration,
      final IPreferenceStore preferenceStore, 
      String fontKey) {
    
    FontUpdater updater = new FontUpdater(viewer, configuration, preferenceStore, fontKey);
    setControlFont(viewer, fontKey);
    return updater;
  }
}
