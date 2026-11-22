import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHRA

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem bruhatHaar_of (hI : IterGauge) (hS : GaugeShift) (hR : RhsLim) : BruhatHaar := by
  intro k r μ μb hμ hμb φ hφ
  obtain ⟨C, hC, hF⟩ := hI k r μ μb hμ hμb
  have hlim1 : Tendsto (fun ρ : ℝ => (μ (gBall k r ρ)).toReal / gVol k r ρ) (𝓝[>] 0) (𝓝 1) := hμ.2
  have hlim2 := (hR k r μb hμb).const_mul (C : ℝ)
  have heq : ∀ᶠ ρ in 𝓝[>] (0:ℝ), (μ (gBall k r ρ)).toReal / gVol k r ρ =
      (C : ℝ) * ((rhs k r μb ((wBall k r ρ).indicator 1)).toReal / gVol k r ρ) := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    obtain ⟨hm, he⟩ := hS k r μ hμ.1 ρ hρ
    have h2 := hF _ (measurable_one.indicator hm)
    rw [lintegral_indicator_one hm, he] at h2
    rw [h2, ENNReal.toReal_mul, ENNReal.coe_toReal, mul_div_assoc]
  have hu := tendsto_nhds_unique (hlim1.congr' heq) hlim2
  have hCr : (C : ℝ) = 2 ^ r := by
    field_simp at hu
    linarith
  rw [hF φ hφ, ← hCr, ENNReal.ofReal_coe_nnreal]
  rfl

theorem bruhatHaar_of_iterGauge (hI : IterGauge) (hS : GaugeShift) (hW : Sandwich) (hV : VolLim) : BruhatHaar :=
  bruhatHaar_of hI hS (rhsLim_of hW hV)

end Formalism.L2.SG.Pf.BH
