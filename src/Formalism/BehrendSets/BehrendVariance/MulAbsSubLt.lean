import Formalism.BehrendSets.Statement

open Finset

namespace Formalism.BehrendSets.Thick

lemma mem_thick {n : ℕ} {T : Finset ℕ} {u p : ZMod n} :
    p ∈ Formalism.BehrendSets.thick n T u ↔ ∃ t ∈ T, ((t : ℕ) : ZMod n) + u = p := by
  simp [Formalism.BehrendSets.thick]

lemma mul_abs_sub_lt {a b c n : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hna : c * a < n) (hnb : c * b < n) : c * |a - b| < n := by
  rw [← abs_of_nonneg hc, ← abs_mul, mul_sub, abs_lt]
  constructor <;> nlinarith

end Formalism.BehrendSets.Thick

namespace Formalism.BehrendSets

end Formalism.BehrendSets
