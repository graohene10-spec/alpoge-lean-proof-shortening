import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.EvalIdBracketCanonical
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QnEvalMap

open MvPolynomial

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem highest_weight_corollary_two : RationalBitableauLatticeStatement := by
  intro n _ mu hmu
  simpa only [qn_nu_cast hmu] using
    qn_main n (qn_nu mu) (qn_nu_anti hmu) (fun I : TIdx mu => brkPol mu I) (canT mu)
      (fun I => bracket_mem_dualWeyl hmu I) (dualWeyl_le_span_bracket hmu) (eval_id_bracket_canonical mu)

end Formalism.InvariantFactorPaths.ColumnFamilies
