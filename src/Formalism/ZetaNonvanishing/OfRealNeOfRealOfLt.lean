import Formalism.ZetaNonvanishing.RiemannZetaOneNeZeroOfRealMemIoo

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

section Fam

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
  (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ)

lemma ofReal_ne_ofReal_of_lt {a b : ℝ} (h : a < b) : (b : ℂ) ≠ (a : ℂ) := by
  exact Complex.ofReal_injective.ne (ne_of_gt h)

lemma ne_ofReal_of_lt_re {s : ℂ} {a : ℝ} (h : a < s.re) : s ≠ (a : ℂ) := by
  exact ne_of_apply_ne Complex.re (by simpa using ne_of_gt h)

end Fam

end Formalism
