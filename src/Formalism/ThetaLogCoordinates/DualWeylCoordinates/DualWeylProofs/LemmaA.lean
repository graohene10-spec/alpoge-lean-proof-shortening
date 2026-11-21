import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementA
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ABridge

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem claimA_straightening : LemmaA := by
  intro n _ mu _ F _
  have hu : IsUnit (mapCoord (n := n) F ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)) :=
    (Units.isUnit _).map _
  have h := (linearIndependent_standard_tableauBideterminant F mu).map' (qa_Phi F n _) (LinearMap.ker_eq_bot.mpr (qa_Phi_inj F n _ hu))
  simpa only [Function.comp_def, qa_mapCoord_brk] using h

end Formalism.InvariantFactorPaths.ColumnFamilies
