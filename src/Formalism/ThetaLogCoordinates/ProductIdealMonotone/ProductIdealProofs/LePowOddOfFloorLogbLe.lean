import Formalism.ThetaLogCoordinates.ProductIdealMonotone.ParamDefs

noncomputable section

open scoped BigOperators Classical

namespace Formalism.InvariantFactorPaths.G0

variable {n : ℕ}

theorem gam_le {p : ℝ} (hp : 5 ≤ p) : gam p ≤ 25 / (24 * p) := by
  unfold gam
  rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
  nlinarith

end Formalism.InvariantFactorPaths.G0
