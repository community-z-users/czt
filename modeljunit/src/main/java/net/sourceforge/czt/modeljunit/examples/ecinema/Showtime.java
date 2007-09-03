package net.sourceforge.czt.modeljunit.examples.ecinema;

import java.util.HashSet;
import java.util.Set;

public class Showtime
{
  public static final int DATE_CORRECT = 1; // not really used yet

  public int dateTime = DATE_CORRECT;
  public boolean buyButtonActive = false;
  public boolean clearAllButtonActive = false;
  public String movie;
  public Set<String> tickets = new HashSet<String>();
  public int ticketsLeft;
}
