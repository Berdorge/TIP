package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.ast._
import tip.cfg._
import tip.lattices.{MapLattice, PowersetLattice}
import tip.solvers.{SimpleMapLatticeFixpointSolver, SimpleWorklistFixpointSolver}

/**
  * Base class for reaching definitions analysis.
  */
abstract class ReachingDefinitionsAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis(true) {
  import tip.ast.AstOps._

  val lattice: MapLattice[CfgNode, PowersetLattice[Definition]] = new MapLattice(new PowersetLattice())

  val domain: Set[CfgNode] = cfg.nodes

  NoPointers.assertContainsProgram(cfg.prog)
  NoRecords.assertContainsProgram(cfg.prog)

  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element =
    n match {
      case r: CfgStmtNode =>
        r.data match {
          case varr: AVarStmt => varr.appearingIds.map(Declaration)
          case as: AAssignStmt =>
            as.left match {
              case id: AIdentifier => s.filterNot(_.declaration == declData(id)) + Assignment(declData(id), as.right)
              case _ => ???
            }
          case _ => s
        }
      case _ => s
    }

  sealed trait Definition {
    def declaration: ADeclaration
  }

  case class Declaration(declaration: ADeclaration) extends Definition
  case class Assignment(declaration: ADeclaration, expression: AExpr) extends Definition
}

/**
  * Reaching definitions analysis that uses the simple fipoint solver.
  */
class ReachingDefinitionsAnalysisSimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends ReachingDefinitionsAnalysis(cfg)
    with SimpleMapLatticeFixpointSolver[CfgNode]
    with ForwardDependencies

/**
  * Reaching definitions analysis that uses the worklist solver.
  */
class ReachingDefinitionsAnalysisWorklistSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends ReachingDefinitionsAnalysis(cfg)
    with SimpleWorklistFixpointSolver[CfgNode]
    with ForwardDependencies
