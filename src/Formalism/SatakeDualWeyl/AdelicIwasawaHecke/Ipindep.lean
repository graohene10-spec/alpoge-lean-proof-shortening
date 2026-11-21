import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

theorem mem_stabAt_mul_iff (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) (δ : Γ) :
    δ ∈ stabAt Γ K ((γ : G) * g * κ) ↔ γ⁻¹ * δ * γ ∈ stabAt Γ K g := by
  simp only [stabAt, Set.mem_setOf_eq]
  have e : ((γ : G) * g * κ)⁻¹ * (δ : G) * ((γ : G) * g * κ) =
      (κ : G)⁻¹ * (g⁻¹ * ((γ⁻¹ * δ * γ : Γ) : G) * g) * κ := by
    push_cast; group
  rw [e, K.mul_mem_cancel_right κ.2, K.mul_mem_cancel_left (K.inv_mem κ.2)]

theorem card_stabAt_mul (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) :
    Nat.card (stabAt Γ K ((γ : G) * g * κ)) = Nat.card (stabAt Γ K g) := by
  refine Nat.card_congr
    (Equiv.subtypeEquiv (MulAut.conj (γ⁻¹ : Γ)).toEquiv fun δ => ?_)
  simpa [MulAut.conj_apply] using mem_stabAt_mul_iff Γ K g γ κ δ

theorem inner_product_independent : Formalism.UG.IpIndep := by
  intro G _ Γ K k _ _ W _ _ ρ _ B hB s s' hs hs' _ f hf f' hf'
  unfold ipAMF
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨γ, hγ, κ, hκ, he⟩ := (DoubleCoset.eq _ _ (s c) (s' c)).1 ((hs c).trans (hs' c).symm)
  rw [show s' c = ((⟨γ, hγ⟩ : Γ) : G) * s c * ((⟨κ, hκ⟩ : K) : G) from he,
    card_stabAt_mul, hf, hf', hB]

end Formalism.UG.P
