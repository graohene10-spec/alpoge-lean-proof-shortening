import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcColESymmVal

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

theorem closure_first_part_of : LemmaA → SBasis → ClosureBasicModules := by
  intro hA hS n _
  exact ⟨fun M h1 h => qc_colFam_triv M h1 h, fun M mu β hmu hβ => qc_colFam_SMu hA hS hmu hβ,
    fun M M' ε _ e h ⟨CF⟩ => qc_colFam_tw M M' ε e h CF⟩

end Formalism.InvariantFactorPaths.ColumnFamilies
