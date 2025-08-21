package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.cfg._
import tip.lattices.IntervalLattice._
import tip.lattices._
import tip.solvers._

trait VariableSizeAnalysisWidening extends ValueAnalysisMisc with Dependencies[CfgNode] {
  val cfg: ProgramCfg

  val valuelattice: IntervalLattice.type

  val liftedstatelattice: LiftLattice[statelattice.type]

  def loophead(n: CfgNode): Boolean = indep(n).exists(cfg.rank(_) > cfg.rank(n))

  def widenInterval(x: valuelattice.Element, y: valuelattice.Element): valuelattice.Element =
    (x, y) match {
      case (IntervalLattice.EmptyInterval, _) => y
      case (_, IntervalLattice.EmptyInterval) => x
      case (_, (l2, h2)) => {
        if (leq(y, x)) {
          return x
        }

        (l2, h2) match {
          case (MInf, IntNum(q)) => widenMInfInterval(q)
          case (IntNum(p), PInf) => widenPInfInterval(p)
          case (IntNum(p), IntNum(q)) => {
            if (q <= p || q == p + 1) {
              return y
            }

            var currentInterval = (Int.MinValue, Int.MaxValue)
            while (true) {
              val nextInterval = findWidenedChild((p, q), currentInterval)
              if (nextInterval == currentInterval) {
                return (IntNum(currentInterval._1), IntNum(currentInterval._2))
              }
              currentInterval = nextInterval
            }
            throw new AssertionError()
          }
          case _ => (l2, h2)
        }
      }
    }

  def widen(x: liftedstatelattice.Element, y: liftedstatelattice.Element): liftedstatelattice.Element =
    (x, y) match {
      case (liftedstatelattice.Bottom, liftedstatelattice.Lift(ym)) =>
        liftedstatelattice.Lift(declaredVars.map { v =>
          v -> widenInterval(valuelattice.bottom, ym(v))
        }.toMap)
      case (liftedstatelattice.Bottom, _) => y
      case (_, liftedstatelattice.Bottom) => x
      case (liftedstatelattice.Lift(xm), liftedstatelattice.Lift(ym)) =>
        liftedstatelattice.Lift(declaredVars.map { v =>
          v -> widenInterval(xm(v), ym(v))
        }.toMap)
    }

  private def widenMInfInterval(endInclusive: Int) =
    Iterator
      .iterate(Int.MinValue) { i =>
        i + (i - Int.MinValue) + 1
      }
      .takeWhile(_ <= -1)
      .find(endInclusive <= _)
      .map { i =>
        (MInf, IntNum(i))
      }
      .getOrElse(FullInterval)

  private def widenPInfInterval(start: Int) =
    Iterator
      .iterate(Int.MaxValue) { i =>
        i + (i - Int.MaxValue) - 1
      }
      .takeWhile(_ >= 0)
      .find(start >= _)
      .map { i =>
        (IntNum(i), PInf)
      }
      .getOrElse(FullInterval)

  private def findWidenedChild(unwidenedInterval: (Int, Int), currentInterval: (Int, Int)) = currentInterval match {
    case (left, right) => {
      val mid = left.toLong.+(right.toLong)./(2).toInt
      val negativeChildSize = math.min(left - mid, mid - right)

      Iterator
        .iterate((left, left - negativeChildSize - 1)) { interval =>
          (interval._1 - negativeChildSize / 2, interval._2 - negativeChildSize / 2)
        }
        .take(3)
        .find(leq(unwidenedInterval, _))
        .getOrElse(currentInterval)
    }
  }
}

object VariableSizeAnalysis {

  object Intraprocedural {

    /**
      * Variable size analysis, using the worklist solver with and widening.
      */
    class WorklistSolverWithWidening(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
        extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, IntervalLattice)
        with WorklistFixpointSolverWithReachabilityAndWidening[CfgNode]
        with VariableSizeAnalysisWidening

    /**
      * Variable size analysis, using the worklist solver with widening and narrowing.
      */
    class WorklistSolverWithWideningAndNarrowing(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
        extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, IntervalLattice)
        with WorklistFixpointSolverWithReachabilityAndWideningAndNarrowing[CfgNode]
        with VariableSizeAnalysisWidening {

      val narrowingSteps = 5
    }
  }
}
