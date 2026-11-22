import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecALogLower
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.HermitianCurvature.StatementB

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def sztJd (ε : Fin n → Bool) : Fin n → ℂ := fun a => if ε a then 1 else -1

theorem szt_Jm_eq (ε : Fin n → Bool) : Jm ε = Matrix.diagonal (sztJd ε) := rfl

theorem szt_jd_sq (ε : Fin n → Bool) (a : Fin n) : sztJd ε a * sztJd ε a = 1 := by
  unfold sztJd
  split_ifs <;> norm_num

theorem szt_lead_Jconj (ε : Fin n → Bool) (z : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) :
    S7.lead i (Jm ε * z * Jm ε) = S7.lead i z := by
  unfold S7.lead
  split_ifs with h
  · have hsub : (Jm ε * z * Jm ε).submatrix (Fin.castLE h) (Fin.castLE h) =
        Matrix.diagonal (sztJd ε ∘ Fin.castLE h) * z.submatrix (Fin.castLE h) (Fin.castLE h) *
          Matrix.diagonal (sztJd ε ∘ Fin.castLE h) := by
      ext a b
      simp only [szt_Jm_eq, Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Function.comp_apply]
    rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hA : (∏ a, (sztJd ε ∘ Fin.castLE h) a) * (∏ a, (sztJd ε ∘ Fin.castLE h) a) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun a _ => szt_jd_sq ε _
    rw [mul_right_comm, hA, one_mul]
  · rfl

theorem szt_phiM_Jconj (ε : Fin n → Bool) (μ : Fin n → ℤ) (z : Matrix (Fin n) (Fin n) ℂ) :
    S7.PhiM μ (Jm ε * z * Jm ε) = S7.PhiM μ z := by
  simp [S7.PhiM, szt_lead_Jconj]

theorem szt_phiM_inv_conj {ε : Fin n → Bool} (μ : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X)
    (k : S7.KG ε) :
    S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k)⁻¹ =
      S7.PhiM μ (S7.toMK k⁻¹ * NormedSpace.exp X * S7.toMK k) := by
  obtain ⟨hY, hE⟩ := S7.inP_conj k⁻¹ hX
  simp only [inv_inv] at hY hE
  rw [← hE, Matrix.inv_eq_left_inv (PolarDecomposition.polar_exp_neg_mul _), ← S7.inP_JXJ hY,
    PolarDecomposition.polar_exp_Jconj, szt_phiM_Jconj]

section Cayley

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}

theorem szt_unitary (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) : Pᴴ * P = 1 ∧ P * Pᴴ = 1 := by
  refine ⟨?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff' (A := P)).mp hP.2
  · simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff (A := P)).mp hP.2

theorem szt_conj_mem (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : P * g * P⁻¹ ∈ UJset ε := by
  rw [← mir_UJset_eq]
  obtain ⟨e1, e2⟩ := szt_unitary hP
  have hc : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  rw [Matrix.inv_eq_left_inv e1]
  calc (P * g * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (P * g * Pᴴ)
      = P * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * Pᴴ := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = P * Pᴴ * Formalism.REAL.Jm ε * (P * Pᴴ) := by
        rw [hc, hg', ← hc]; simp [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [e2]; simp

theorem szt_hs_conj (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    S7.hs (P * g * P⁻¹) = S7.hs g := by
  obtain ⟨e1, -⟩ := szt_unitary hP
  have h := S7.decA_hs_conj (K := Pᴴ) (by rw [Matrix.conjTranspose_conjTranspose]; exact e1) g
  rw [Matrix.inv_eq_left_inv e1]
  simpa only [Matrix.conjTranspose_conjTranspose] using h

end Cayley

theorem szt_gN_eq {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.FourierDecayAlt.B.gN g = Real.sqrt (S7.hs g) := by
  simp [Formalism.FourierDecayAlt.B.gN, S7.hs, Complex.normSq_eq_norm_sq]

end ReciprocityTheory.ChartRestriction.DS
