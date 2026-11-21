import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbBasisApply

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem filtration_theorem_one_of : LemmaA → ColumnFamilyStandardVectorsBasis := by
  intro hA n _ M CF
  refine ⟨?_, fun R _ => qb_basisR hA CF R⟩
  simpa only [qb_vecF_int] using qb_basisR hA CF ℤ

end Formalism.InvariantFactorPaths.ColumnFamilies
