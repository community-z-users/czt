
package net.sourceforge.czt.animation.common.factory;

import net.sourceforge.czt.animation.common.analyzer.Analyzer;
import net.sourceforge.czt.animation.common.analyzer.ZLiveAnalyzer;
import net.sourceforge.czt.animation.common.evaluator.Evaluator;
import net.sourceforge.czt.animation.common.evaluator.ZLiveEvaluator;
import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.z.util.Factory;

/**
 * @author Linan Zhang
 *
 */
public class GaffeFactory
{
  private static ZLive zLive = new ZLive();

  private static Analyzer analyzer = new ZLiveAnalyzer();

  private static Evaluator evaluator = new ZLiveEvaluator();

  /**
   * No instance, solid
   */
  private GaffeFactory()
  {
  }

  /**
   * @return
   */
  public static Analyzer getAnalyzer()
  {
    return analyzer;
  }

  /**
   * @return
   */
  public static Evaluator getEvaluator()
  {
    return evaluator;
  }

  /**
   * @return
   */
  public static Factory getFactory()
  {
    return zLive.getFactory();
  }

  /**
   * @return Returns the zLive.
   */
  public static ZLive getZLive()
  {
    return zLive;
  }
}
