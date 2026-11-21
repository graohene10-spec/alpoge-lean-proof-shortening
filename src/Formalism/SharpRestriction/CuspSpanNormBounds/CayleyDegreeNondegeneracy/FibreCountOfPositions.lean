import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PairsModuloNormFixedQuadruple

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem c3eqv_mem_orth (U : Submodule E S.V) (x : S.V) : x ∈ orth S U ↔ ∀ v ∈ U, S.hT v x = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem c3eqv_gmap_iff (n : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap n Λ = Λ ↔ (∀ y ∈ Λ, n y ∈ Λ) ∧ ∀ y ∈ Λ, n.symm y ∈ Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rw [← h]
      exact ⟨y, hy, rfl⟩
    · rw [← h] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      simpa using hz
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact h1 z hz
    · intro y hy
      exact ⟨n.symm y, h2 y hy, by simp⟩

theorem c3eqv_symm_mem (n : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) (h : ∀ x ∈ U, n x ∈ U) :
    ∀ x ∈ U, n.symm x ∈ U := by
  have hle : U.map (n : S.V →ₗ[E] S.V) ≤ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : U.map (n : S.V →ₗ[E] S.V) = U :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n U)
  intro x hx
  have hx' : x ∈ U.map (n : S.V →ₗ[E] S.V) := heq.symm ▸ hx
  obtain ⟨y, hy, rfl⟩ := hx'
  simpa using hy

theorem c3eqv_isom_symm {n : S.V ≃ₗ[E] S.V} (h : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) : n.symm ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  intro x y
  simpa using (h (n.symm x) (n.symm y)).symm

theorem c3eqv_isom_trans {n m : S.V ≃ₗ[E] S.V} (h : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (h' : m ∈ Formalism.HermitianLatticesTheory.isom S.hT) :
    n.trans m ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  intro x y
  simpa using (h' (n x) (n y)).trans (h x y)

theorem c3eqv_orth_map {n : S.V ≃ₗ[E] S.V} (h : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (U₁ U₂ : Submodule E S.V)
    (hU : ∀ v ∈ U₂, n.symm v ∈ U₁) {x : S.V} (hx : x ∈ orth S U₁) : n x ∈ orth S U₂ := by
  rw [c3eqv_mem_orth] at hx ⊢
  intro v hv
  simpa using (h (n.symm v) x).trans (hx (n.symm v) (hU v hv))

variable {T : E} (F : LFlag S r T)

theorem c3eqv_Xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  unfold Xflag Formalism.MainNotions.S.FlagG.Xa
  exact Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < j) => Nat.lt_succ_of_lt hi)

theorem c3eqv_Xflag_zero : Xflag F 0 = ⊥ := by
  simp [Xflag, Formalism.MainNotions.S.FlagG.Xa]

theorem c3eqv_Xsp_eq : Xsp F = Xflag F r := by
  unfold Xsp Xflag Formalism.MainNotions.S.FlagG.X Formalism.MainNotions.S.FlagG.Xa
  congr 1
  ext v
  simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq, Fin.is_lt, true_and]

variable {F} {Λ : Submodule (𝓞 E) S.V}

theorem c3eqv_N_flag {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (j : ℕ) : ∀ x ∈ Xflag F j, n x ∈ Xflag F j := by
  unfold NLam at hn
  simp only [Set.mem_setOf_eq] at hn
  obtain ⟨_, h1, _⟩ := hn
  intro x hx
  cases j with
  | zero =>
    rw [c3eqv_Xflag_zero] at hx ⊢
    simpa using congrArg n ((Submodule.mem_bot E).1 hx)
  | succ j =>
    have h2 := c3eqv_Xflag_mono F j (h1 j x hx)
    rw [← sub_add_cancel (n x) x]
    exact Submodule.add_mem _ h2 hx

theorem c3eqv_N_X {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : ∀ x ∈ Xsp F, n x ∈ Xsp F := by
  simpa [c3eqv_Xsp_eq] using c3eqv_N_flag hn r

theorem c3eqv_N_orth {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : ∀ x ∈ orth S (Xsp F), n x ∈ orth S (Xsp F) := by
  have hX := c3eqv_N_X hn
  have h' := hn
  simp only [NLam, Set.mem_setOf_eq, IsAutLam] at h'
  exact fun x hx => c3eqv_orth_map h'.1.1 _ _ (c3eqv_symm_mem n _ hX) hx

theorem c3eqv_NLam_trans {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F) : n.trans m ∈ NLam Λ F := by
  have hnf := c3eqv_N_flag hn
  have hno := c3eqv_N_orth hn
  have hn' := hn
  have hm' := hm
  simp only [NLam, Set.mem_setOf_eq, IsAutLam] at hn' hm' ⊢
  obtain ⟨⟨hni, hng⟩, hn1, hn2⟩ := hn'
  obtain ⟨⟨hmi, hmg⟩, hm1, hm2⟩ := hm'
  refine ⟨⟨c3eqv_isom_trans hni hmi, ?_⟩, ?_, ?_⟩
  · rw [c3eqv_gmap_iff] at hng hmg ⊢
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · simpa only [LinearEquiv.trans_apply] using hmg.1 _ (hng.1 _ hy)
    · simpa only [LinearEquiv.symm_trans_apply] using hng.2 _ (hmg.2 _ hy)
  · intro j x hx
    have e : (n.trans m) x - x = (m (n x) - n x) + (n x - x) := by
      simp only [LinearEquiv.trans_apply]
      abel
    rw [e]
    exact Submodule.add_mem _ (hm1 j _ (hnf (j + 1) x hx)) (hn1 j x hx)
  · intro x hx
    have e : (n.trans m) x - x = (m (n x) - n x) + (n x - x) := by
      simp only [LinearEquiv.trans_apply]
      abel
    rw [e]
    exact Submodule.add_mem _ (hm2 _ (hno x hx)) (hn2 x hx)

theorem c3eqv_NLam_symm {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : n.symm ∈ NLam Λ F := by
  have hnf := c3eqv_N_flag hn
  have hno := c3eqv_N_orth hn
  have hn' := hn
  simp only [NLam, Set.mem_setOf_eq, IsAutLam] at hn' ⊢
  obtain ⟨⟨hni, hng⟩, hn1, hn2⟩ := hn'
  refine ⟨⟨c3eqv_isom_symm hni, ?_⟩, ?_, ?_⟩
  · rw [c3eqv_gmap_iff] at hng ⊢
    simpa [LinearEquiv.symm_symm] using ⟨hng.2, hng.1⟩
  · intro j x hx
    have hy := c3eqv_symm_mem n _ (hnf (j + 1)) x hx
    have e : n.symm x - x = -(n (n.symm x) - n.symm x) := by
      rw [LinearEquiv.apply_symm_apply]
      abel
    rw [e]
    exact Submodule.neg_mem _ (hn1 j _ hy)
  · intro x hx
    have hy := c3eqv_symm_mem n _ hno x hx
    have e : n.symm x - x = -(n (n.symm x) - n.symm x) := by
      rw [LinearEquiv.apply_symm_apply]
      abel
    rw [e]
    exact Submodule.neg_mem _ (hn2 _ hy)

def isUnitriangularIntegral {N : ℕ} (ξ : Matrix (Fin N) (Fin N) (𝓞 E)) : Prop :=
  (∀ a b, b < a → ξ a b = 0) ∧ ∀ a, ξ a a = 1

end Gen

section D7

variable (D : D7)

variable (Λ : LatV D) {T T' : D.host.E} (F : LFlag (hS D) D.R.rS T)

end D7

end Formalism.MainNotions.BridgeLemma₂

end
