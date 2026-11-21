import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.NilpotentSubgroup

open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.SW

open PI PI.QuotSetU

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}

def inW (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

lemma mulVec_bvec_apply (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (g *ᵥ bvec j) i = g i j := by
  simp [bvec]

lemma bvec_apply (i j : Fin (2 * r + k + 1)) : bvec j i = if i = j then 1 else 0 := by
  simp [bvec, Pi.single_apply]

lemma uw_col_out {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (j : Fin (2 * r + k + 1)) (hj : ¬ inW k r j) (i : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by
  simp only [UWset, Set.mem_setOf_eq] at hh
  obtain ⟨-, hfix, -⟩ := hh
  have key : h *ᵥ bvec j = bvec j := by
    unfold inW at hj
    by_cases hjr : j.val < r
    · have h1 := (hfix ⟨j.val, hjr⟩).1
      have e : eI k r ⟨j.val, hjr⟩ = j := Fin.ext rfl
      rwa [e] at h1
    · have ha : 2 * r + k - j.val < r := by
        have := j.isLt
        omega
      have h1 := (hfix ⟨2 * r + k - j.val, ha⟩).2
      have e : esI k r ⟨2 * r + k - j.val, ha⟩ = j := by
        apply Fin.ext
        show 2 * r + k - (2 * r + k - j.val) = j.val
        have := j.isLt
        omega
      rwa [e] at h1
  rw [← mulVec_bvec_apply h i j, key, bvec_apply]

lemma piI_not_inW {i : Fin (2 * r + k + 1)} (hi : ¬ inW k r i) : ¬ inW k r (piI k r i) := by
  unfold inW at hi ⊢
  unfold piI
  rw [if_neg hi]
  show ¬ (r ≤ 2 * r + k - i.val ∧ 2 * r + k - i.val ≤ r + k)
  have := i.isLt
  omega

private lemma Hpk_applyUnitaryQuotientCompactness (i x : Fin (2 * r + k + 1)) :
    Hpk k r i x = if x = piI k r i then (if i.val = r + k then (-1 : ℂ) else 1) else 0 := by
  simpa [epsI] using Hpk_apply (k := k) (r := r) i x

private lemma piI_piI' (i : Fin (2 * r + k + 1)) : piI k r (piI k r i) = i := by
  exact piI_piI i

lemma uw_block {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (i j : Fin (2 * r + k + 1)) (hij : ¬ (inW k r i ∧ inW k r j)) :
    h i j = if i = j then 1 else 0 := by
  by_cases hj : inW k r j
  · have hi : ¬ inW k r i := fun h' => hij ⟨h', hj⟩
    have hne : i ≠ j := fun e => hi (by rw [e]; exact hj)
    rw [if_neg hne]
    have hh' := hh
    simp only [UWset, Set.mem_setOf_eq] at hh'
    have hU : hᴴ * Hpk k r * h = Hpk k r := hh'.1
    have hp := piI_not_inW hi
    have hcol : ∀ x, h x (piI k r i) = if x = piI k r i then 1 else 0 :=
      fun x => uw_col_out hh _ hp x
    have hrowp : ∀ y, (hᴴ * Hpk k r) (piI k r i) y = Hpk k r (piI k r i) y := by
      intro y
      rw [Matrix.mul_apply, Finset.sum_eq_single (piI k r i)]
      · rw [Matrix.conjTranspose_apply, hcol, if_pos rfl, star_one, one_mul]
      · intro x _ hx
        rw [Matrix.conjTranspose_apply, hcol, if_neg hx, star_zero, zero_mul]
      · intro hm
        exact absurd (Finset.mem_univ _) hm
    have e := congrFun (congrFun hU (piI k r i)) j
    rw [Matrix.mul_apply] at e
    simp only [hrowp] at e
    rw [Finset.sum_eq_single i] at e
    · rw [Hpk_applyUnitaryQuotientCompactness (piI k r i) i, Hpk_applyUnitaryQuotientCompactness (piI k r i) j, piI_piI', if_pos rfl,
        if_neg (Ne.symm hne)] at e
      have hc : (if (piI k r i).val = r + k then (-1 : ℂ) else 1) ≠ 0 := by
        split_ifs <;> norm_num
      exact (mul_eq_zero.mp e).resolve_left hc
    · intro y _ hy
      rw [Hpk_applyUnitaryQuotientCompactness (piI k r i) y, piI_piI', if_neg hy, zero_mul]
    · intro hm
      exact absurd (Finset.mem_univ _) hm
  · exact uw_col_out hh j hj i

lemma one_mem_UW : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
  simp only [UWset, UH, Set.mem_setOf_eq]
  refine ⟨by simp, fun a => ⟨by simp, by simp⟩, by simp⟩

lemma mul_mem_UW {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UWset k r z) (hb : b ∈ UWset k r z) : a * b ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq] at ha hb ⊢
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨mul_mem_UH ha1 hb1, fun i => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hb2 i).1, (ha2 i).1]
  · rw [← Matrix.mulVec_mulVec, (hb2 i).2, (ha2 i).2]
  · rw [← Matrix.mulVec_mulVec, hb3, ha3]

private lemma sign_mul_sign_piI_eq_one (i : Fin (2 * r + k + 1)) :
    (if i.val = r + k then (-1 : ℂ) else 1) *
      (if (piI k r i).val = r + k then (-1 : ℂ) else 1) = 1 := by
  change epsI k r i * epsI k r (piI k r i) = 1
  rw [epsI_piI, epsI_mul_self]

private lemma Hpk_mul_Hpk : Hpk k r * Hpk k r = 1 := by
  exact Hpk_mul_self

lemma inv_fix {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : a ∈ UH (Hpk k r))
    {v : Fin (2 * r + k + 1) → ℂ} (hv : a *ᵥ v = v) : a⁻¹ *ᵥ v = v := by
  rw [inv_eq_UH hU]
  calc (Hpk k r * aᴴ * Hpk k r) *ᵥ v = (Hpk k r * aᴴ * Hpk k r) *ᵥ (a *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, inv_mul_UH hU, Matrix.one_mulVec]

lemma inv_mem_UW {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UWset k r z) : a⁻¹ ∈ UWset k r z := by
  simp only [UWset, Set.mem_setOf_eq] at ha ⊢
  obtain ⟨ha1, ha2, ha3⟩ := ha
  exact ⟨inv_mem_UH ha1, fun i => ⟨inv_fix ha1 (ha2 i).1, inv_fix ha1 (ha2 i).2⟩, inv_fix ha1 ha3⟩

lemma uw_sub_S {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h ∈ Sset k r z := by
  simp only [Sset, Set.mem_setOf_eq]
  refine ⟨h, hh, 1, ?_, (Matrix.mul_one h).symm⟩
  exact (mem_Nset_iff 1).2 ⟨one_mem_UH, nc_one⟩

lemma n_sub_S {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r) :
    n ∈ Sset k r z := by
  simp only [Sset, Set.mem_setOf_eq]
  exact ⟨1, one_mem_UW, n, hn, (Matrix.one_mul n).symm⟩

end PI.QuotSetU.UnitaryGroupMassFormula.SW
