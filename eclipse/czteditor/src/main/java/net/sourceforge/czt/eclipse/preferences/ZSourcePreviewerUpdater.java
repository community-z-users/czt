
package net.sourceforge.czt.eclipse.preferences;

import net.sourceforge.czt.eclipse.editors.ZSourceViewerConfiguration;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.graphics.Font;

/**
 * Handles Z fEditor font changes for Z source preview viewers.
 * 
 * @since 3.0
 * 
 * @author Chengdong Xu
 */
public class ZSourcePreviewerUpdater
{

  /**
   * Creates a Z source preview updater for the given viewer, configuration and preference store.
   *
   * @param viewer the viewer
   * @param configuration the configuration
   * @param preferenceStore the preference store
   */
  public ZSourcePreviewerUpdater(final SourceViewer viewer,
      final ZSourceViewerConfiguration configuration,
      final IPreferenceStore preferenceStore)
  {
    Assert.isNotNull(viewer);
    Assert.isNotNull(configuration);
    Assert.isNotNull(preferenceStore);
    final IPropertyChangeListener fontChangeListener = new IPropertyChangeListener()
    {
      /*
       * @see org.eclipse.jface.util.IPropertyChangeListener#propertyChange(org.eclipse.jface.util.PropertyChangeEvent)
       */
      public void propertyChange(PropertyChangeEvent event)
      {
        if (event.getProperty().equals(PreferenceConstants.EDITOR_TEXT_FONT)) {
          Font font = JFaceResources
              .getFont(PreferenceConstants.EDITOR_TEXT_FONT);
          viewer.getTextWidget().setFont(font);
        }
      }
    };
    final IPropertyChangeListener propertyChangeListener = new IPropertyChangeListener()
    {
      /*
       * @see org.eclipse.jface.util.IPropertyChangeListener#propertyChange(org.eclipse.jface.util.PropertyChangeEvent)
       */
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
      /*
       * @see org.eclipse.swt.events.DisposeListener#widgetDisposed(org.eclipse.swt.events.DisposeEvent)
       */
      public void widgetDisposed(DisposeEvent e)
      {
        preferenceStore.removePropertyChangeListener(propertyChangeListener);
        JFaceResources.getFontRegistry().removeListener(fontChangeListener);
      }
    });
    JFaceResources.getFontRegistry().addListener(fontChangeListener);
    preferenceStore.addPropertyChangeListener(propertyChangeListener);
  }
}
