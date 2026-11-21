import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.FrameMemLocP

noncomputable section

open scoped Classical

namespace PI.TCS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def Tr (γ : S.V ≃ₗ[E] S.V) (A₂ A : Submodule (𝓞 E) S.V) : Prop := ∀ v, v ∈ A₂ ↔ γ.symm v ∈ A

def TrE (γ : S.V ≃ₗ[E] S.V) (U₂ U : Submodule E S.V) : Prop := ∀ v, v ∈ U₂ ↔ γ.symm v ∈ U

variable {γ : S.V ≃ₗ[E] S.V}

theorem Tr.inf {A₂ A B₂ B : Submodule (𝓞 E) S.V} (hA : Tr γ A₂ A) (hB : Tr γ B₂ B) :
    Tr γ (A₂ ⊓ B₂) (A ⊓ B) := by
  intro v
  rw [Submodule.mem_inf, Submodule.mem_inf, hA v, hB v]

theorem Tr.sup {A₂ A B₂ B : Submodule (𝓞 E) S.V} (hA : Tr γ A₂ A) (hB : Tr γ B₂ B) :
    Tr γ (A₂ ⊔ B₂) (A ⊔ B) := by
  intro v
  simp only [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨γ.symm y, (hA y).1 hy, γ.symm z, (hB z).1 hz, (map_add _ _ _).symm⟩
  · rintro ⟨y, hy, z, hz, hyz⟩
    refine ⟨γ y, (hA _).2 (by simpa using hy), γ z, (hB _).2 (by simpa using hz), ?_⟩
    rw [← map_add, hyz, LinearEquiv.apply_symm_apply]

theorem TrE.toO {U₂ U : Submodule E S.V} (h : TrE γ U₂ U) : Tr γ (toO S U₂) (toO S U) := by
  exact h

theorem Tr.localization₂ {p : Ideal (𝓞 E)} [p.IsPrime] {A₂ A : Submodule (𝓞 E) S.V} (h : Tr γ A₂ A) :
    Tr γ (Formalism.HermitianLatticesTheory.localization₂ p A₂) (Formalism.HermitianLatticesTheory.localization₂ p A) := by
  intro v
  rw [mem_locP, mem_locP]
  refine exists_congr (fun s => and_congr_right (fun _ => ?_))
  rw [h, lin_osmul]

theorem Tr.eq {A₂ A B₂ B : Submodule (𝓞 E) S.V} (hA : Tr γ A₂ A) (hB : Tr γ B₂ B) (h : A = B) :
    A₂ = B₂ := by
  ext v
  rw [hA, hB, h]

theorem mem_span_image_equiv {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (β : M ≃ₗ[R] M)
    (s : Set M) (v : M) : v ∈ Submodule.span R (β '' s) ↔ β.symm v ∈ Submodule.span R s := by
  rw [show (β '' s) = (β : M →ₗ[R] M) '' s from rfl, Submodule.span_image, Submodule.mem_map_equiv]

theorem Tr.span {s₂ s : Set S.V} (h : s₂ = γ '' s) : Tr γ (Submodule.span (𝓞 E) s₂) (Submodule.span (𝓞 E) s) := by
  subst h
  exact mem_span_image_equiv (γ.restrictScalars (𝓞 E)) s

theorem TrE.span {s₂ s : Set S.V} (h : s₂ = γ '' s) : TrE γ (Submodule.span E s₂) (Submodule.span E s) := by
  subst h
  exact mem_span_image_equiv γ s

theorem tr_of_gmap {Λ : Submodule (𝓞 E) S.V} (h : Formalism.HermitianLatticesTheory.gmap γ Λ = Λ) : Tr γ Λ Λ := by
  intro v
  constructor
  · intro hv
    rw [← h] at hv
    unfold Formalism.HermitianLatticesTheory.gmap at hv
    rw [Submodule.mem_map] at hv
    obtain ⟨y, hy, rfl⟩ := hv
    simpa using hy
  · intro hv
    rw [← h]
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.mem_map]
    exact ⟨γ.symm v, hv, by simp⟩

theorem TrE.perp {U₂ U : Submodule E S.V} (h : TrE γ U₂ U) (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b) :
    TrE γ (Formalism.MainNotions.S.Lat.orth S U₂) (Formalism.MainNotions.S.Lat.orth S U) := by
  intro v
  simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hv y hy
    have hgy : γ y ∈ U₂ := (h _).2 (by simpa using hy)
    rw [← hiso y (γ.symm v), LinearEquiv.apply_symm_apply]
    exact hv _ hgy
  · intro hv y hy
    have h1 := hv _ ((h y).1 hy)
    rw [← hiso, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    exact h1

variable {T' : E} {x F₂ : LFlag S r T'}

theorem trE_Xsp (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) : TrE γ (Xsp F₂) (Xsp x) := by
  refine TrE.span ?_
  rw [← Set.range_comp]
  exact congrArg Set.range (funext he)

theorem tr_XLam (Λ : Submodule (𝓞 E) S.V) (hΛ : Tr γ Λ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) :
    Tr γ (XLam Λ F₂) (XLam Λ x) := by
  simpa only [XLam] using Tr.inf hΛ (TrE.toO (trE_Xsp he))

theorem tr_Lsub (Λ : Submodule (𝓞 E) S.V) (hΛ : Tr γ Λ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k))
    (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b) : Tr γ (Lsub Λ F₂) (Lsub Λ x) := by
  have hX := trE_Xsp he
  have hO := TrE.toO (TrE.perp hX hiso)
  simpa only [Lsub, Lrep] using Tr.inf (Tr.sup (Tr.inf hΛ hO) (TrE.toO hX)) hO

theorem isLift_tr (Λ : Submodule (𝓞 E) S.V) (hΛ : Tr γ Λ Λ) (hz : F₂.fl.z = γ x.fl.z)
    (hzt : F₂.zt = γ x.zt) (hx : IsLift Λ x) : IsLift Λ F₂ := by
  refine ⟨?_, ?_⟩
  · simpa [hz] using (hΛ (γ x.fl.z)).2 (by simpa using hx.1)
  · rw [hzt, hz, hx.2]

theorem fixedConv_tr (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (hΛ : Tr γ Λ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k))
    (hz : F₂.fl.z = γ x.fl.z) (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b) (hx : IsFixedConv Λ g x) :
    IsFixedConv Λ g F₂ := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨fun P => ?_, fun c hc => ?_⟩
  · obtain ⟨c, hc0, hc1, hloc⟩ := h1 P
    haveI := P.isPrime
    refine ⟨c, hc0, hc1, ?_⟩
    exact Tr.eq (Tr.localization₂ (tr_XLam Λ hΛ he))
      (Tr.localization₂ (Tr.span (by
        rw [← Set.range_comp]
        congr 1
        funext a
        simp [he a]))) hloc
  · apply h2 c
    simpa [hz] using (tr_Lsub Λ hΛ he hiso (c • F₂.fl.z)).1 hc

end Gen

end PI.TCS
