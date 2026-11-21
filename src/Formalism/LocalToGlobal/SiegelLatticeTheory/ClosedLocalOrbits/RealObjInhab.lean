import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

noncomputable section

open Matrix

namespace Formalism.L2.SG.RealObj

theorem Dl_diagonal {r : ℕ} (c : Fin (r + 1) → ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    Dl (Matrix.diagonal c) l = ∏ i : Fin l, c (Fin.castLE hl i) := by
  simp [Dl, hl, Matrix.submatrix_diagonal c (Fin.castLE hl) (Fin.castLE_injective hl), Matrix.det_diagonal]

theorem Gv_pos_example : 0 < Gv 1 1 (Matrix.diagonal (![1, 2] : Fin 2 → ℂ)) := by
  unfold Gv
  rw [Dl_diagonal _ 2 le_rfl, Dl_diagonal _ 1 (by norm_num)]
  norm_num [Fin.prod_univ_two, Fin.prod_univ_one]

theorem JacV_diag_one (c : Fin 2 → ℂ) : JacV (Matrix.diagonal c) = (‖c 0‖ ^ 2) ^ 2 := by
  unfold JacV
  rw [Finset.Icc_self, Finset.prod_singleton, Dl_diagonal _ 1 (by norm_num), Fin.prod_univ_one]
  rfl

theorem ZhatO_signs (Z : Matrix (Fin 2) (Fin 2) ℂ) : ZhatO Z 0 0 = -Z 0 0 ∧ ZhatO Z 0 1 = Z 0 1 := by
  refine ⟨?_, ?_⟩ <;> simp [ZhatO]

theorem famSc_last {n r : ℕ} (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    famSc sc e z (Fin.last r) = z := by
  simp [famSc, fam]

theorem trG_one {n : ℕ} {ε : Fin n → Bool} (γ : Formalism.REAL.UJ ε) :
    trG (1 : Matrix (Fin n) (Fin n) ℂ) 1 γ = Formalism.MainNotions.S.uMat γ := by
  simp only [trG, one_mul, mul_one]

example : Formalism.L2.SG.DataInst.signAux (K := ℤ) 2 1 [(1, 5), (2, 7)] = [(1, 5), (2, 7)] := by decide

example : Formalism.L2.SG.DataInst.signAux (K := ℤ) 3 1 [(1, 5), (1, 6), (2, 7)] = [(1, -5), (1, 6), (2, 7)] := by decide

example : Formalism.L2.SG.DataInst.signAux (K := ℤ) 3 1 (Formalism.L2.SG.DataInst.signAux 3 1 [(1, 5), (1, 6), (2, 7)]) =
    [(1, 5), (1, 6), (2, 7)] := by decide

end Formalism.L2.SG.RealObj
