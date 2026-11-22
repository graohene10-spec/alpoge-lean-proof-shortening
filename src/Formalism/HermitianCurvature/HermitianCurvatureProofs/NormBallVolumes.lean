import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftingTheory

open Matrix MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.NormBallVolumes

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem gnLower : GNLower := fun _ _ _ hg => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg

theorem gN_meas (k r : ℕ) : Measurable fun g : Mt k r => gN (Matrix.of g) := by
  unfold gN
  exact Measurable.sqrt (Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => Complex.continuous_normSq.measurable.comp ((measurable_pi_apply j).comp (measurable_pi_apply i)))

theorem ae_mem {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ g ∂μ, Matrix.of g ∈ U := by
  rw [ae_iff]
  exact h.conc

theorem one_mem (k r : ℕ) : (1 : Mat k r) ∈ GV k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

def iv {k r : ℕ} (g : Mat k r) : Mat k r := Hpk k r * gᴴ * Hpk k r

theorem iv_mul {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : iv g * g = 1 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold iv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.Hsq k r

theorem iv_mem {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : iv g ∈ GV k r := by
  simpa [← Matrix.inv_eq_left_inv (iv_mul hg)] using Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg

theorem sigmaFinite_of_haar {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem lmulM_cont {k r : ℕ} (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  exact (continuous_const (y := a)).matrix_mul (continuous_id : Continuous fun x : Mt k r => (Matrix.of x : Mat k r))

theorem volCrude : VolCrude :=
  _root_.UpperTheory.Reformulated.B.LiftingTheory.volCrude

theorem shellInt : ShellInt := by
  intro X _ μ N C d A hN h1 hd hV hA
  have hmeas : ∀ k : ℕ, MeasurableSet {x : X | N x ≤ (2 : ℝ) ^ (k + 1)} := fun k =>
    measurableSet_le hN measurable_const
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (N x ^ (-A)) ≤
      ∑' k : ℕ, {x : X | N x ≤ (2 : ℝ) ^ (k + 1)}.indicator
        (fun _ => ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-A))) x := by
    filter_upwards [h1] with x hx
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hx (one_lt_two : (1 : ℝ) < 2)
    refine le_trans ?_ (ENNReal.le_tsum k)
    rw [Set.indicator_of_mem (show x ∈ {x : X | N x ≤ (2 : ℝ) ^ (k + 1)} from hk2.le)]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos (by positivity) hk1 (by linarith : -A ≤ 0))
  have hr : (2 : ℝ) ^ (d - A) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^ (d - A) := by positivity
  have hsum : Summable fun k : ℕ => C * (2 : ℝ) ^ d * ((2 : ℝ) ^ (d - A)) ^ k :=
    (summable_geometric_of_lt_one hr0 hr).mul_left _
  have hterm : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ (-A) * (C * ((2 : ℝ) ^ (k + 1)) ^ d) =
      C * (2 : ℝ) ^ d * ((2 : ℝ) ^ (d - A)) ^ k := by
    intro k
    have hk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    rw [pow_succ, Real.mul_rpow hk.le two_pos.le, Real.rpow_pow_comm two_pos.le, sub_eq_add_neg,
      Real.rpow_add hk]
    ring
  calc ∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μ
      ≤ ∫⁻ x, ∑' k : ℕ, {x : X | N x ≤ (2 : ℝ) ^ (k + 1)}.indicator
        (fun _ => ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-A))) x ∂μ :=
        MeasureTheory.lintegral_mono_ae hpt
    _ = ∑' k : ℕ, ENNReal.ofReal (((2 : ℝ) ^ k) ^ (-A)) *
        μ {x : X | N x ≤ (2 : ℝ) ^ (k + 1)} := by
        rw [MeasureTheory.lintegral_tsum
          (fun k => (measurable_const.indicator (hmeas k)).aemeasurable)]
        exact tsum_congr fun k => MeasureTheory.lintegral_indicator_const (hmeas k) _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (C * (2 : ℝ) ^ d * ((2 : ℝ) ^ (d - A)) ^ k) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [← hterm k, ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact hV _ (one_le_pow₀ one_le_two)
    _ < ⊤ := hsum.tsum_ofReal_lt_top

end Formalism.FourierDecayAlt.P.NormBallVolumes

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.NormBallVolumes

theorem norm_power_integrable_crude_of_volume : Formalism.FourierDecayAlt.B2.GNIntCrudeFromVol := by
  intro hS hL hV k r μG A hμ hA
  obtain ⟨C, hC⟩ := hV k r μG hμ
  refine hS (Mt k r) μG (fun g => gN (Matrix.of g)) C _ A (gN_meas k r) ?_ (by positivity) hC hA
  filter_upwards [ae_mem hμ] with g hg using hL k r _ hg

theorem matrix_coefficient_bound_by_norm : Formalism.FourierDecayAlt.B2.CCFromGN := by
  intro k r Wp Wq _ _ _ _ D A h F c _ hb
  have hae : ∀ᵐ g ∂D.μG, ‖F (Matrix.of g)‖ₑ ≤ ENNReal.ofReal |c| * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) := by
    filter_upwards [ae_mem D.haarG] with g hg
    have h1 := hb _ hg
    have hpos : 0 < gN (Matrix.of g) := lt_of_lt_of_le one_pos (gnLower k r _ hg)
    have hp : 0 < gN (Matrix.of g) ^ A := Real.rpow_pos_of_pos hpos A
    rw [← ENNReal.ofReal_mul (abs_nonneg c), ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ hp]
    simpa [mul_comm] using h1.trans (le_abs_self c)
  calc (∫⁻ g : Mt k r, ‖F (Matrix.of g)‖ₑ ∂D.μG)
      ≤ ∫⁻ g : Mt k r, ENNReal.ofReal |c| * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG := lintegral_mono_ae hae
    _ = ENNReal.ofReal |c| * ∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem matrix_coefficient_integrable_of_parts : Formalism.FourierDecayAlt.B2.AssembleCCInt := by
  intro h1 h2 k r Wp Wq _ _ _ _ D A hA
  exact h1 k r Wp Wq D A (h2 k r D.μG A D.haarG hA)

theorem matrix_coefficient_integrable_double : Formalism.FourierDecayAlt.B2.CCIntDouble := by
  intro hX k r Wp Wq _ _ _ _ _ _ D A hA
  by_cases hT : ∃ T : Wq →L[ℂ] Wp, T ≠ 0
  · obtain ⟨T, hT0⟩ := hT
    apply matrix_coefficient_bound_by_norm k r Wp Wq D A
    have hA1 : AB k r ≤ A / 2 := by linarith
    obtain ⟨Ξ, ⟨C, hC⟩, _⟩ := hX k r Wp Wq D (A / 2) hA1
    set F : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((gN g ^ (-(A / 2)) : ℝ) : ℂ) • T with hF
    have hm : AEStronglyMeasurable (fun g : Mt k r => F (Matrix.of g)) D.μG := by
      have h1 : Measurable fun g : Mt k r => ((gN (Matrix.of g) ^ (-(A / 2)) : ℝ) : ℂ) :=
        Complex.measurable_ofReal.comp ((gN_meas k r).pow_const _)
      exact h1.aestronglyMeasurable.smul_const T
    have hn : ∀ g : Mat k r, 0 < gN g → ‖F g‖ = gN g ^ (-(A / 2)) * ‖T‖ := by
      intro g hg
      simp only [hF, norm_smul, Complex.norm_real]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hg.le _)]
    have hb : ∀ g ∈ GV k r, gN g ^ (A / 2) * ‖F g‖ ≤ ‖T‖ := by
      intro g hg
      have hpos : 0 < gN g := lt_of_lt_of_le one_pos (gnLower k r g hg)
      rw [hn g hpos, ← mul_assoc, ← Real.rpow_add hpos]
      simp
    have hmain := hC F F ‖T‖ ‖T‖ hm hm hb hb 1 (one_mem k r) 1 (one_mem k r)
    have key : ∀ᵐ g ∂D.μG, ‖T‖ₑ * ‖T‖ₑ * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) =
        ‖F ((1 : Mat k r)⁻¹ * Matrix.of g * 1)‖ₑ * ‖F (Matrix.of g)‖ₑ := by
      filter_upwards [ae_mem D.haarG] with g hg
      have hpos : 0 < gN (Matrix.of g) := lt_of_lt_of_le one_pos (gnLower k r _ hg)
      have e1 : (1 : Mat k r)⁻¹ * Matrix.of g * 1 = Matrix.of g := by simp
      rw [e1, ← ofReal_norm (F (Matrix.of g)), hn _ hpos, ← ofReal_norm T,
        ← ENNReal.ofReal_mul (norm_nonneg T), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : gN (Matrix.of g) ^ (-A) = gN (Matrix.of g) ^ (-(A / 2)) * gN (Matrix.of g) ^ (-(A / 2)) := by
        rw [← Real.rpow_add hpos]; congr 1; ring
      rw [this]; ring
    have hfin : (∫⁻ g : Mt k r, ‖T‖ₑ * ‖T‖ₑ * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG) < ∞ := by
      rw [lintegral_congr_ae key]
      refine lt_of_le_of_lt hmain ?_
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top) ENNReal.coe_lt_top
    have hc : ‖T‖ₑ * ‖T‖ₑ ≠ ∞ := ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
    rw [lintegral_const_mul' _ _ hc] at hfin
    rcases ENNReal.mul_lt_top_iff.mp hfin with h | h | h
    · exact h.2
    · exfalso
      have : ‖T‖ₑ = 0 := by
        rcases mul_eq_zero.mp h with h | h <;> exact h
      exact hT0 (enorm_eq_zero.mp this)
    · rw [h]; exact ENNReal.zero_lt_top
  · simp only [not_exists, not_not] at hT
    intro F c _ _
    simp [hT]

theorem matrix_coefficient_integrable_crude_all : Formalism.FourierDecayAlt.B2.CCIntCrudeAll := by
  intro k r Wp Wq _ _ _ _ D A hA
  exact matrix_coefficient_bound_by_norm k r Wp Wq D A
    (norm_power_integrable_crude_of_volume shellInt gnLower volCrude k r D.μG A D.haarG hA)

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.NormBallVolumes

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

end Formalism.FourierDecayAlt.P.NormBallVolumes
