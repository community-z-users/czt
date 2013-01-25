package net.sourceforge.czt.eclipse.ui.internal.editors;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.internal.preferences.PreferenceConstants;
import net.sourceforge.czt.session.Dialect;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.ListenerList;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;


/**
 * A singleton implementation of Z Dialect support functionality. 
 * The object loads available dialect character tables and provides 
 * listener notifications when dialect changes in preferences.
 * 
 * @author Andrius Velykis
 */
public enum ZDialectSupport {

  INSTANCE;

  public enum ZDialect {
    Z(Dialect.Z.toString(), "Z", "etc/ZTable.xml"), 
    OBJECT_Z(Dialect.OZ.toString(), "Object Z", "etc/ObjectZTable.xml"), 
    CIRCUS(Dialect.CIRCUS.toString(), "Circus", "etc/CircusTable.xml"),  
    CIRCUSTIME(Dialect.CIRCUSTIME.toString(), "Circus Time", "etc/CircusTimeTable.xml"), 
    ZEVES(Dialect.ZEVES.toString(), "Z/EVES", "etc/ZEvesTable.xml");

    private final String dialect;
    private final String label;
    private final IPath path;

    private ZDialect(String dialect, String label, String path)
    {
      this.dialect = dialect;
      this.label = label;
      this.path = new Path(path);
    }

    public String getDialect()
    {
      return dialect;
    }

    public String getLabel()
    {
      return label;
    }

    private IPath getPath()
    {
      return path;
    }

    public static ZDialect find(String dialect)
    {
      for (ZDialect table : ZDialect.values()) {
        if (table.getDialect().equals(dialect)) {
          return table;
        }
      }

      // use Z by default
      return Z;
    }
  }

  private final Map<ZDialect, ZCharTable> dialectTables = new HashMap<ZDialect, ZCharTable>();

  private final ListenerList dialectChangedListeners = new ListenerList();
  
  private final IPropertyChangeListener prefsListener = new IPropertyChangeListener()
  {

    @Override
    public void propertyChange(PropertyChangeEvent event)
    {
      String key = event.getProperty();
      if (key.equals(PreferenceConstants.PROP_DIALECT)) {
        String value = String.valueOf(event.getNewValue());
        fireSessionInitialised(value);
      }
    }
  };

  private ZDialectSupport()
  {
    for (ZDialect tableId : ZDialect.values()) {
      dialectTables.put(tableId, new ZCharTable(tableId.getPath()));
    }
  }
  
  private IPreferenceStore getPrefs() {
    return CztUIPlugin.getDefault().getPreferenceStore();
  }

  public List<ZDialect> getTableIds()
  {
    return Arrays.asList(ZDialect.values());
  }

  public Collection<ZCharTable> getCharacterTables()
  {
    return Collections.unmodifiableCollection(dialectTables.values());
  }

  public ZCharTable getCharacterTable(ZDialect tableId)
  {
    return dialectTables.get(tableId);
  }

  public ZCharTable getCharacterTable(String dialect)
  {
    return getCharacterTable(ZDialect.find(dialect));
  }
  
  public String getCurrentDialect() {
    return getPrefs().getString(PreferenceConstants.PROP_DIALECT);
  }
  
  public ZDialect getCurrentDialectTableId() {
    return ZDialect.find(getCurrentDialect());
  }

  public void addDialectChangedListener(IDialectChangedListener listener)
  {
    dialectChangedListeners.add(listener);
    getPrefs().addPropertyChangeListener(prefsListener);
  }

  public void removeDialectChangedListener(IDialectChangedListener listener)
  {
    dialectChangedListeners.remove(listener);
    
    if (dialectChangedListeners.isEmpty()) {
      // remove prefs listener
      getPrefs().removePropertyChangeListener(prefsListener);
    }
  }

  private void fireSessionInitialised(String newDialect)
  {
    for (Object listener : dialectChangedListeners.getListeners()) {
      ((IDialectChangedListener) listener).dialectChanged(newDialect);
    }
  }
  
}
