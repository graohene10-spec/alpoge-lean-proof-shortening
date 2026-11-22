import Formalism.CyclotomicNorms.StatementI

open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

namespace Sqf

variable {K : Type} [Field K]

lemma coeff_monicOf_lt {N : ℕ} (a : Fin N → K) (i : Fin N) :
    (monicOf a).coeff (i : ℕ) = a i := by
  unfold monicOf
  simp only [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.2), zero_add, finset_sum_coeff, coeff_C_mul_X_pow]
  simpa using Finset.sum_eq_single i (fun j _ hj => if_neg (fun h => hj (Fin.ext h).symm)) (by simp)

lemma coeff_monicOf_ge {N : ℕ} (a : Fin N → K) (k : ℕ) (hk : N ≤ k) :
    (monicOf a).coeff k = if k = N then 1 else 0 := by
  unfold monicOf
  simp only [coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_zero (fun j _ => if_neg (by have := j.2; omega)), add_zero]

lemma natDegree_monicOf {N : ℕ} (a : Fin N → K) : (monicOf a).natDegree = N := by
  unfold monicOf
  rw [natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt a), natDegree_X_pow]

lemma monic_monicOf {N : ℕ} (a : Fin N → K) : (monicOf a).Monic := by
  simpa only [monicOf] using monic_X_pow_add (degree_sum_fin_lt a)

lemma monicOf_coeffs (p : K[X]) (hp : p.Monic) {m : ℕ} (hd : p.natDegree = m) :
    monicOf (fun i : Fin m => p.coeff i) = p := by
  ext n
  rcases lt_or_ge n m with h | h
  · exact coeff_monicOf_lt (fun i : Fin m => p.coeff i) ⟨n, h⟩
  · rw [coeff_monicOf_ge _ n h]
    rcases eq_or_lt_of_le h with rfl | hlt
    · rw [if_pos rfl, ← hd, hp.coeff_natDegree]
    · rw [if_neg (ne_of_gt hlt), coeff_eq_zero_of_natDegree_lt (by omega)]

lemma decomp (f : K[X]) (hf : f.Monic) (h0 : f.coeff 0 ≠ 0) (hsq : ¬ Squarefree f) :
    ∃ P h : K[X], P.Monic ∧ h.Monic ∧ 1 ≤ P.natDegree ∧ P.coeff 0 ≠ 0 ∧ f = P * P * h := by
  unfold Squarefree at hsq
  push_neg at hsq
  obtain ⟨x, ⟨g, hg⟩, hx⟩ := hsq
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hf.ne_zero (by simpa using hg)
  have hc : x.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hx0
  have hP : (x * C x.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hx0
  have hu : C x.leadingCoeff⁻¹ * C x.leadingCoeff = (1 : K[X]) := by
    rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  have key : f = (x * C x.leadingCoeff⁻¹) * (x * C x.leadingCoeff⁻¹) *
      (C x.leadingCoeff * C x.leadingCoeff * g) := by
    rw [hg]
    linear_combination (-(x * x * g * (C x.leadingCoeff⁻¹ * C x.leadingCoeff + 1))) * hu
  refine ⟨x * C x.leadingCoeff⁻¹, C x.leadingCoeff * C x.leadingCoeff * g, hP,
    Monic.of_mul_monic_left (hP.mul hP) (by rw [← key]; exact hf), ?_, ?_, key⟩
  · rw [Nat.one_le_iff_ne_zero]
    intro hdeg
    exact hx (isUnit_iff_exists_inv.mpr ⟨_, (Monic.natDegree_eq_zero hP).mp hdeg⟩)
  · intro hz
    exact h0 (by rw [key, mul_coeff_zero, mul_coeff_zero, hz]; simp)

lemma geo (q : ℕ) (hq : 2 ≤ q) (N : ℕ) :
    ∀ k, k < N → (∑ d ∈ Icc 1 k, q ^ (N - d)) + 2 * q ^ (N - 1 - k) ≤ 2 * q ^ (N - 1) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ih' := ih (by omega)
    rw [show N - (k + 1) = N - 1 - k by omega]
    rw [show N - 1 - k = (N - 1 - (k + 1)) + 1 by omega, pow_succ] at ih' ⊢
    linarith [Nat.mul_le_mul_left (q ^ (N - 1 - (k + 1))) hq]

end Sqf

end Formalism.CyclotomicNorms
