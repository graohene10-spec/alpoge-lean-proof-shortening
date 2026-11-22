import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSFA

open MeasureTheory
open scoped NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def HaarUniqueSF : Prop :=
  ∀ (k r : ℕ) (U : Set (Mat k r)) (μ₀ μ : Measure (Mt k r)), IsClosedSubgroup U → Formalism.FourierDecayAlt.B.IsHaarOn U μ₀ →
    Formalism.MainNotions.S.IsHaarOn U μ → ∃ c : ℝ≥0, c ≠ 0 ∧ μ = c • μ₀

theorem haarUniqueSF' : HaarUniqueSF := by
  intro k r U μ₀ μ hU h₀ hμ
  have : Fact (IsClosedSubgroup U) := ⟨hU⟩
  obtain ⟨hσ, hne, hconc, hleft⟩ := hμ
  have : IsFiniteMeasureOnCompacts μ₀ := ⟨h₀.finite_compact⟩
  have := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ
  have := HaarSigmaFiniteUniqueness.sigmaFinite_comap (U := U) μ₀
  have := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap (U := U) μ hconc hleft
  have := HaarSigmaFiniteUniqueness.isMulLeftInvariant_comap (U := U) μ₀ h₀.conc h₀.left
  have hμS : μ.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Mt k r) ≠ 0 := fun h0 => hne (by
    rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ hconc, h0, Measure.map_zero])
  have hνS : μ₀.comap (Subtype.val : HaarSigmaFiniteUniqueness.Aset U → Mt k r) ≠ 0 := fun h0 => h₀.ne_zero (by
    rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ₀ h₀.conc, h0, Measure.map_zero])
  obtain ⟨c, hc0, hc⟩ := HaarSigmaFiniteUniqueness.eq_smul_of_sigmaFinite _ _ hμS hνS
  refine ⟨c, hc0, ?_⟩
  rw [← HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ hconc, hc, Measure.map_smul,
    HaarSigmaFiniteUniqueness.map_comap_val (U := U) μ₀ h₀.conc]

theorem haarUniqueSF (_h : UnitaryGroupStructuralFacts) : HaarUniqueSF := haarUniqueSF'

end ReciprocityTheory.ChartRestriction.DS.Mult1
