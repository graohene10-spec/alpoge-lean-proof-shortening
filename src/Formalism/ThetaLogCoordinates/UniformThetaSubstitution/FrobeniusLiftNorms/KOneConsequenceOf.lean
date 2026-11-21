import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

namespace FormalGroupLawNegation

open FormalGroupLaws

theorem integral_X {K ι : Type} [NormedField K] (x : ι) :
    Integral (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  by_cases h : n = Finsupp.single x 1 <;> simp [MvPowerSeries.coeff_X, h]

theorem integral_neg {K ι : Type} [NormedField K] {f : MvPowerSeries ι K} (hf : Integral f) :
    Integral (-f) := by
  intro n
  rw [map_neg, norm_neg]
  exact hf n

end FormalGroupLawNegation

open FormalGroupLawNegation FormalGroupLaws

end Formalism.InvariantFactorPaths.G7
