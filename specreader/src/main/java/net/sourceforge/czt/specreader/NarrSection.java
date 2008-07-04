package net.sourceforge.czt.specreader;

/**
 * Records the details of a narrative section.
 * 
 * @author ian
 */
public final class NarrSection extends Section
{
  /** Narrative */
  private InformalParaBlock para_;

  /**
   * Constructs a narrative section.
   * 
   * @param filename name of file from which section was read
   * @param isBufferingWanted whether to buffer whole section's text in memory
   * @param para narrative
   */
  public NarrSection(String filename, boolean isBufferingWanted, InformalParaBlock para)
  {
    super(filename, isBufferingWanted);
    para_ = para;
  }

  /**
   * Returns the text of the section,
   * preceded by a %%Zfile directive to say where the text came from.
   */
  @Override
  public String toString()
  {
    final StringBuilder stringBuilder = initializeWriter();
    blockAppend(stringBuilder, para_);
    final String result = stringBuilder.toString();
    finalizeWriter();
    return result;
  }
}
