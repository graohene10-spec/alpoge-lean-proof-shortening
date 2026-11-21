import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ExistsKhwGenSubOfKType
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeHW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}

theorem data_lowK_eq (hgap : StdGap ε lam) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (S : Submodule ℂ H) (hS : S ≤ closGen E V)
    (hST : Formalism.MainNotions.S.IsKTypeOf ε σ (lowK ε lam) S) : S = V.map D.subtype := by
  have hSK' : ∀ k ∈ Kset ε, ∀ x ∈ S, σ k x ∈ S :=
    fun k hk x hx => hST.2.1 k (by rw [mir_Kset_eq]; exact hk) x hx
  have hSM : S ≤ (genSub E V).map D.subtype := data_kfin_le hgap hσ hD hV hc hVK S hS hST.1 hSK'
  have hSD : S ≤ D := fun x hx => by
    obtain ⟨y, -, rfl⟩ := Submodule.mem_map.1 (hSM hx)
    exact y.2
  obtain ⟨w, hwS, hw0, hwhw⟩ := exists_isKHWVec_of_isKTypeOf hσ hD hST hSD
  have hwG : w ∈ genSub E V := by
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hSM hwS)
    exact (Subtype.ext hyw) ▸ hy
  have hwV : w ∈ V :=
    khw_lowK_mem hD.glRep (isInfUnitary_of_isDerivedOn hσ hD) hV hc hgap hwG hwhw
  have hTK : Formalism.MainNotions.S.IsKStableOn ε σ (V.map D.subtype) := by
    intro g hg x hx
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨u, hu, huv⟩ := hVK g (by simpa [mir_Kset_eq] using hg) v hv
    exact Submodule.mem_map.2 ⟨u, hu, by simpa using huv⟩
  have hwT : (w : H) ∈ V.map D.subtype := Submodule.mem_map_of_mem hwV
  have hwne : ∀ T : Submodule ℂ H, (w : H) ∈ T → T ≠ ⊥ := by
    intro T hT h
    exact hw0 ((Submodule.coe_eq_zero).1 ((Submodule.mem_bot ℂ).1 (h ▸ hT)))
  have hwTinf : (w : H) ∈ S ⊓ V.map D.subtype := Submodule.mem_inf.2 ⟨hwS, hwT⟩
  have hTKinf : Formalism.MainNotions.S.IsKStableOn ε σ (S ⊓ V.map D.subtype) :=
    fun g hg x hx => Submodule.mem_inf.2
      ⟨hST.2.1 g hg x (Submodule.mem_inf.1 hx).1, hTK g hg x (Submodule.mem_inf.1 hx).2⟩
  have hT : S ⊓ V.map D.subtype = S := by
    rcases hST.2.2.1 (S ⊓ V.map D.subtype) inf_le_left hTKinf with h | h
    · exact absurd h (hwne _ hwTinf)
    · exact h
  have hT' : S ⊓ V.map D.subtype = V.map D.subtype := by
    rcases (data_isKTypeOf hgap hσ hD hV hc hVK).2.2.1 (S ⊓ V.map D.subtype) inf_le_right hTKinf with h | h
    · exact absurd h (hwne _ hwTinf)
    · exact h
  exact hT.symm.trans hT'

end ReciprocityTheory.ChartRestriction.DS
