import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.IteratedDerivOrbit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.InKRealSmul

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def brIdxSum (v : Fin n → ℝ) : ℝ := ∑ i : Fin n, ((i : ℕ) : ℝ) * v i

theorem brIdxSum_sub (u v : Fin n → ℝ) : brIdxSum (u - v) = brIdxSum u - brIdxSum v := by
  simp only [brIdxSum, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem brIdxSum_add (u v : Fin n → ℝ) : brIdxSum (u + v) = brIdxSum u + brIdxSum v := by
  simp only [brIdxSum, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem brIdxSum_root (a b : Fin n) : brIdxSum (Formalism.REAL.root a b) = (a : ℕ) - (b : ℕ) := by
  simp [brIdxSum, Formalism.REAL.root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

theorem brIdxSum_cdom_sum (ε : Fin n → Bool) (c : Fin n → Fin n → ℕ)
    (_hc : ∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) :
    brIdxSum (∑ a, ∑ b, (c a b : ℝ) • Formalism.REAL.root a b) = ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) := by
  have hsmul : ∀ (r : ℝ) (v : Fin n → ℝ), brIdxSum (r • v) = r * brIdxSum v := by
    intro r v
    simp only [brIdxSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → Fin n → ℝ),
      brIdxSum (∑ x ∈ s, f x) = ∑ x ∈ s, brIdxSum (f x) := by
    intro ι s f
    simp only [brIdxSum, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_comm
  simp only [hsum, hsmul, brIdxSum_root]

theorem br_cdom_term_nonpos (ε : Fin n → Bool) (c : Fin n → Fin n → ℕ)
    (hc : ∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) (a b : Fin n) :
    (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) ≤ 0 := by
  by_cases h0 : c a b = 0
  · simp [h0]
  · exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (sub_nonpos.mpr (by exact_mod_cast ((hc a b h0).1.le : (a : ℕ) ≤ (b : ℕ))))

theorem brIdxSum_nonpos_of_cdom {ε : Fin n → Bool} {μ Λ : Fin n → ℝ} (h : Formalism.MainNotions.S.CDom ε μ Λ) :
    brIdxSum (Λ - μ) ≤ 0 := by
  unfold Formalism.MainNotions.S.CDom at h
  obtain ⟨c, hc, hΛ⟩ := h
  rw [hΛ, brIdxSum_cdom_sum ε c hc]
  exact Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => br_cdom_term_nonpos ε c hc a b

theorem not_cdom_add_root (ε : Fin n → Bool) (Λ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ Formalism.MainNotions.S.CDom ε (Λ + root a b) Λ := by
  intro h
  have h1 := brIdxSum_nonpos_of_cdom h
  have hr : root a b = Formalism.REAL.root a b := rfl
  rw [brIdxSum_sub, brIdxSum_add, hr, brIdxSum_root] at h1
  have h3 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast (hab : (a : ℕ) < (b : ℕ))
  linarith

theorem cdom_antisymm (ε : Fin n → Bool) {μ Λ : Fin n → ℝ} (h₁ : Formalism.MainNotions.S.CDom ε μ Λ)
    (h₂ : Formalism.MainNotions.S.CDom ε Λ μ) : μ = Λ := by
  unfold Formalism.MainNotions.S.CDom at h₁
  obtain ⟨c, hc, hΛ⟩ := h₁
  have hB : brIdxSum (Λ - μ) = ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) := by
    rw [hΛ, brIdxSum_cdom_sum ε c hc]
  have hsum0 : ∑ a, ∑ b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) = 0 := by
    apply le_antisymm
    · exact Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => br_cdom_term_nonpos ε c hc a b
    · linarith [brIdxSum_sub μ Λ, brIdxSum_sub Λ μ, brIdxSum_nonpos_of_cdom h₂, hB]
  have hterm : ∀ a b, (c a b : ℝ) * ((a : ℕ) - (b : ℕ) : ℝ) = 0 := by
    intro a b
    have h0 := (Finset.sum_eq_zero_iff_of_nonpos (fun a _ => Finset.sum_nonpos fun b _ =>
      br_cdom_term_nonpos ε c hc a b)).1 hsum0 a (Finset.mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => br_cdom_term_nonpos ε c hc a b)).1 h0 b
      (Finset.mem_univ _)
  have hc0 : ∀ a b, c a b = 0 := by
    intro a b
    by_contra hne
    rcases mul_eq_zero.mp (hterm a b) with h | h
    · exact hne (by exact_mod_cast h)
    · have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by
        exact_mod_cast ((hc a b hne).1 : (a : ℕ) < (b : ℕ))
      linarith
  have h5 : Λ - μ = 0 := by
    rw [hΛ]
    simp [hc0]
  exact (sub_eq_zero.mp h5).symm

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem br_actM_mem_of_kStable (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (S : Submodule ℂ D)
    (hS : FiniteDimensional ℂ S) (hK : ∀ k ∈ Kset ε, ∀ v ∈ S, ∃ w ∈ S, (w : H) = σ k v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) {v : D} (hv : v ∈ S) : actM E X v ∈ S := by
  classical
  have hG : Xᴴ * Jm ε + Jm ε * X = 0 := hX.1
  have hXJ : X * Jm ε = Jm ε * X := hX.2
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hXH : Xᴴ = -X := by
    have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by
      rw [hXJ]
      exact eq_neg_of_add_eq_zero_left hG
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJJ, mul_one]
      _ = -X := by rw [h1, neg_mul, mul_assoc, hJJ, mul_one]
  have hexpK : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := by
    intro t
    have hYH : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := by
      rw [Matrix.conjTranspose_smul, hXH, smul_neg]
      congr 2
      simp [Complex.conj_ofReal]
    have hcomm : Commute ((t : ℂ) • X) (-((t : ℂ) • X)) := (Commute.refl _).neg_right
    have hYJ : Commute ((t : ℂ) • X) (Jm ε) := (USum.inK_real_smul hX t).2
    simp only [Kset, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hYH,
        ← Matrix.exp_add_of_commute _ _ hcomm, add_neg_cancel, NormedSpace.exp_zero]
    · exact hYJ.exp_left
  haveI := hS
  have hWc : IsClosed ((LinearMap.range (D.subtype.comp S.subtype) : Submodule ℂ H) : Set H) :=
    Submodule.closed_of_finiteDimensional _
  have hmem : ∀ t : ℝ, σ (NormedSpace.exp ((t : ℂ) • X)) (v : H) ∈
      LinearMap.range (D.subtype.comp S.subtype) := by
    intro t
    obtain ⟨w, hw, hwv⟩ := hK _ (hexpK t) v hv
    exact LinearMap.mem_range.mpr ⟨⟨w, hw⟩, hwv⟩
  have hd := hD.deriv X hX.1 v
  have hlim : ((actM E X v : D) : H) ∈ LinearMap.range (D.subtype.comp S.subtype) :=
    hWc.mem_of_tendsto hd.tendsto_slope_zero (Filter.Eventually.of_forall fun t =>
      Submodule.smul_of_tower_mem _ t⁻¹ (Submodule.sub_mem _ (hmem _) (hmem _)))
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hlim
  have hy' : (y : D) = actM E X v := Subtype.ext (by simpa using hy)
  rw [← hy']
  exact y.2

theorem isKStableSub_of_kStable (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (S : Submodule ℂ D)
    (hS : FiniteDimensional ℂ S) (hK : ∀ k ∈ Kset ε, ∀ v ∈ S, ∃ w ∈ S, (w : H) = σ k v) :
    IsKStableSub ε E S := by
  classical
  intro a b hab v hv
  let X₁ : Matrix (Fin n) (Fin n) ℂ := USum.zM a b 1
  let X₂ : Matrix (Fin n) (Fin n) ℂ := USum.zM a b Complex.I
  have hX₁ : inK ε X₁ := USum.inK_zM hab 1
  have hX₂ : inK ε X₂ := USum.inK_zM hab Complex.I
  have m₁ := br_actM_mem_of_kStable hσ hD S hS hK hX₁ hv
  have m₂ := br_actM_mem_of_kStable hσ hD S hS hK hX₂ hv
  have e₁ : actM E X₁ v = E a b v - E b a v := by
    simp [X₁, USum.actM_zM]
  have e₂ : actM E X₂ v = Complex.I • E a b v + Complex.I • E b a v := by
    simp [X₂, USum.actM_zM, Complex.star_def, Complex.conj_I]
  have e₃ : E a b v = (1 / 2 : ℂ) • (actM E X₁ v - Complex.I • actM E X₂ v) := by
    rw [e₁, e₂, smul_add, smul_smul, smul_smul, Complex.I_mul_I]
    module
  rw [e₃]
  exact S.smul_mem _ (S.sub_mem m₁ (S.smul_mem _ m₂))

end Rep

end ReciprocityTheory.ChartRestriction.DS
