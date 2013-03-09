/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.preferences;

import org.eclipse.core.runtime.ListenerList;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;

/**
 * Adapts {@link org.eclipse.core.runtime.Preferences} to
 * {@link org.eclipse.jface.preference.IPreferenceStore}
 *
 * @author Chengdong Xu
 */
@SuppressWarnings("deprecation")
public class PreferencesAdapter implements IPreferenceStore
{

  /**
   * Property change listener. Listens for events of type
   * {@link org.eclipse.core.runtime.Preferences.PropertyChangeEvent} and fires
   * a {@link org.eclipse.jface.util.PropertyChangeEvent} on the
   * adapter with arguments from the received event.
   */
private class PropertyChangeListener
      implements
        org.eclipse.core.runtime.Preferences.IPropertyChangeListener
        // TODO: deprecated! FIX!
  {

    /*
     * @see org.eclipse.core.runtime.Preferences.IPropertyChangeListener#propertyChange(org.eclipse.core.runtime.Preferences.PropertyChangeEvent)
     */
    public void propertyChange(org.eclipse.core.runtime.Preferences.PropertyChangeEvent event)
    {
      firePropertyChangeEvent(event.getProperty(), event.getOldValue(), event
          .getNewValue());
    }
  }

  /** Listeners on the adapter */
  private ListenerList fListeners = new ListenerList();

  /** Listener on the adapted Preferences */
  private PropertyChangeListener fListener = new PropertyChangeListener();

  /** Adapted Preferences */
private org.eclipse.core.runtime.Preferences fPreferences;

  /** True iff no events should be forwarded */
  private boolean fSilent;

  /**
   * Initialize with empty Preferences.
   */
  public PreferencesAdapter()
  {
    this(new org.eclipse.core.runtime.Preferences());
  }

  /**
   * Initialize with the given org.eclipse.core.runtime.Preferences.
   *
   * @param preferences The preferences to wrap.
   */
  public PreferencesAdapter(org.eclipse.core.runtime.Preferences preferences)
  {
    fPreferences = preferences;
  }

  /**
   * {@inheritDoc}
   */
  public void addPropertyChangeListener(IPropertyChangeListener listener)
  {
    if (fListeners.size() == 0)
      fPreferences.addPropertyChangeListener(fListener);
    fListeners.add(listener);
  }

  /**
   * {@inheritDoc}
   */
  public void removePropertyChangeListener(IPropertyChangeListener listener)
  {
    fListeners.remove(listener);
    if (fListeners.size() == 0)
      fPreferences.removePropertyChangeListener(fListener);
  }

  /**
   * {@inheritDoc}
   */
  public boolean contains(String name)
  {
    return fPreferences.contains(name);
  }

  /**
   * {@inheritDoc}
   */
  public void firePropertyChangeEvent(String name, Object oldValue,
      Object newValue)
  {
    if (!fSilent) {
      PropertyChangeEvent event = new PropertyChangeEvent(this, name, oldValue,
          newValue);
      Object[] listeners = fListeners.getListeners();
      for (int i = 0; i < listeners.length; i++)
        ((IPropertyChangeListener) listeners[i]).propertyChange(event);
    }
  }

  /**
   * {@inheritDoc}
   */
  public boolean getBoolean(String name)
  {
    return fPreferences.getBoolean(name);
  }

  /**
   * {@inheritDoc}
   */
  public boolean getDefaultBoolean(String name)
  {
    return fPreferences.getDefaultBoolean(name);
  }

  /**
   * {@inheritDoc}
   */
  public double getDefaultDouble(String name)
  {
    return fPreferences.getDefaultDouble(name);
  }

  /**
   * {@inheritDoc}
   */
  public float getDefaultFloat(String name)
  {
    return fPreferences.getDefaultFloat(name);
  }

  /**
   * {@inheritDoc}
   */
  public int getDefaultInt(String name)
  {
    return fPreferences.getDefaultInt(name);
  }

  /**
   * {@inheritDoc}
   */
  public long getDefaultLong(String name)
  {
    return fPreferences.getDefaultLong(name);
  }

  /**
   * {@inheritDoc}
   */
  public String getDefaultString(String name)
  {
    return fPreferences.getDefaultString(name);
  }

  /**
   * {@inheritDoc}
   */
  public double getDouble(String name)
  {
    return fPreferences.getDouble(name);
  }

  /**
   * {@inheritDoc}
   */
  public float getFloat(String name)
  {
    return fPreferences.getFloat(name);
  }

  /**
   * {@inheritDoc}
   */
  public int getInt(String name)
  {
    return fPreferences.getInt(name);
  }

  /**
   * {@inheritDoc}
   */
  public long getLong(String name)
  {
    return fPreferences.getLong(name);
  }

  /**
   * {@inheritDoc}
   */
  public String getString(String name)
  {
    return fPreferences.getString(name);
  }

  /**
   * {@inheritDoc}
   */
  public boolean isDefault(String name)
  {
    return fPreferences.isDefault(name);
  }

  /**
   * {@inheritDoc}
   */
  public boolean needsSaving()
  {
    return fPreferences.needsSaving();
  }

  /**
   * {@inheritDoc}
   */
  public void putValue(String name, String value)
  {
    try {
      fSilent = true;
      fPreferences.setValue(name, value);
    } finally {
      fSilent = false;
    }
  }

  /**
   * {@inheritDoc}
   */
  public void setDefault(String name, double value)
  {
    fPreferences.setDefault(name, value);
  }

  /**
   * {@inheritDoc}
   */
  public void setDefault(String name, float value)
  {
    fPreferences.setDefault(name, value);
  }

  /**
   * {@inheritDoc}
   */
  public void setDefault(String name, int value)
  {
    fPreferences.setDefault(name, value);
  }

  /**
   * {@inheritDoc}
   */
  public void setDefault(String name, long value)
  {
    fPreferences.setDefault(name, value);
  }

  /**
   * {@inheritDoc}
   */
  public void setDefault(String name, String defaultObject)
  {
    fPreferences.setDefault(name, defaultObject);
  }

  /**
   * {@inheritDoc}
   */
  public void setDefault(String name, boolean value)
  {
    fPreferences.setDefault(name, value);
  }

  /**
   * {@inheritDoc}
   */
  public void setToDefault(String name)
  {
    fPreferences.setToDefault(name);
  }

  /**
   * {@inheritDoc}
   */
  public void setValue(String name, double value)
  {
    fPreferences.setValue(name, value);
  }

  /**
   * {@inheritDoc}
   */
  public void setValue(String name, float value)
  {
    fPreferences.setValue(name, value);
  }

  /**
   * {@inheritDoc}
   */
  public void setValue(String name, int value)
  {
    fPreferences.setValue(name, value);
  }

  /**
   * {@inheritDoc}
   */
  public void setValue(String name, long value)
  {
    fPreferences.setValue(name, value);
  }

  /**
   * {@inheritDoc}
   */
  public void setValue(String name, String value)
  {
    fPreferences.setValue(name, value);
  }

  /**
   * {@inheritDoc}
   */
  public void setValue(String name, boolean value)
  {
    fPreferences.setValue(name, value);
  }

}
