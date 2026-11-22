import Mathlib

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

theorem key_bound {X Y M K b : ℝ} {E : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hM : 1 ≤ M) (hK : 0 < K) (hE : 0 < E)
    (hb : 0 ≤ b) (h : X + Y ≤ K * M ^ E) :
    M ^ (-b) ≤ K ^ (b / E) * (X ^ (-(b / (2 * E))) * Y ^ (-(b / (2 * E)))) := by
  have hE' : (0 : ℝ) < E := by exact_mod_cast hE
  have hs0 : 0 ≤ b / E := div_nonneg hb hE'.le
  have hXY0 : 0 < X * Y := by nlinarith
  have hsq : Real.sqrt (X * Y) ≤ K * M ^ E := by
    calc Real.sqrt (X * Y) ≤ Real.sqrt ((X + Y) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = X + Y := Real.sqrt_sq (by linarith)
      _ ≤ K * M ^ E := h
  have hpow : (X * Y) ^ (b / (2 * E)) ≤ K ^ (b / E) * M ^ b := by
    calc (X * Y) ^ (b / (2 * E)) = Real.sqrt (X * Y) ^ (b / E) := by
          rw [show b / (2 * E) = (1 / 2) * (b / E) by ring, Real.rpow_mul hXY0.le,
            ← Real.sqrt_eq_rpow]
      _ ≤ (K * M ^ E) ^ (b / E) := Real.rpow_le_rpow (Real.sqrt_nonneg _) hsq hs0
      _ = K ^ (b / E) * M ^ b := by
        rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul (by linarith)]
        congr 2
        field_simp
  have hA : 0 < (X * Y) ^ (b / (2 * E)) := Real.rpow_pos_of_pos hXY0 _
  have hM0 : 0 < M ^ b := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith), Real.rpow_neg (by linarith),
    ← mul_inv, ← Real.mul_rpow (by linarith) (by linarith), ← div_eq_mul_inv,
    le_div_iff₀ hA, inv_mul_le_iff₀ hM0]
  linarith

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
