import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BigCellDiagIff
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def JacEx : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    ∃ h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε, IsSecLoc ε sc e z z' T T' h ∧
      ∀ μS μS' : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS → IsHaarS (SLoc ε e z') μS' →
        ∃ C, 0 < C ∧ DisintLoc ε k T T' μS μS' h C

def GoodPos {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) : Prop :=
  ∃ f : Fin r → Fin n → ℂ, (∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) ∧ (∀ a b, hJ ε (f a) (f b) = 0) ∧
    ∀ a, hJ ε (f a) z = 0 ∧ hJ ε (f a) z' = 0

def JacExGood : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → GoodPos ε e z z' → 0 < sc →
    ∃ h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε, IsSecLoc ε sc e z z' T T' h ∧
      ∀ μS μS' : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS → IsHaarS (SLoc ε e z') μS' →
        ∃ C, 0 < C ∧ DisintLoc ε k T T' μS μS' h C

def HpkEx : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z → 0 < Formalism.QuantumDeterminants.Tz k r z' →
    ∀ μ μW μW' μN : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μ →
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z') μW' →
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    ∀ μsec, Formalism.QuantumDeterminants.IsSection k r z z' μsec →
    ∃ K : ℝ, 0 < K ∧ ∀ φ : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, Measurable φ →
      ∫⁻ x, φ x ∂μ = ENNReal.ofReal K * ∫⁻ q : (Fin r → ℂ) × ℂ,
        ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r (Formalism.QuantumDeterminants.Tz k r z) (Formalism.QuantumDeterminants.Tz k r z') q) *
          ∫⁻ s, ∫⁻ s', φ (fun i j => (Matrix.of s * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * (Matrix.of s')⁻¹) i j)
            ∂(Formalism.MainNotions.S.muS μW' μN) ∂(Formalism.MainNotions.S.muS μW μN)

def TransEx : Prop := HpkEx → RightInvS → JacExGood

def DegRed : Prop := RightInvS → JacExGood → JacEx

theorem jacLoc_of_ex (h1 : DiagDCLoc) (hR : RightInvS) (hE : JacEx) : JacLoc := by
  intro n r k ε e z z' T T' sc hF hsc μS μS' hμ hμ' h hh
  obtain ⟨h0, hh0, hD⟩ := hE n r k ε e z z' T T' sc hF hsc
  obtain ⟨C, hC, hDC⟩ := hD μS μS' hμ hμ'
  have hF' : FrameLoc ε k e z' z T' T := frameLoc_swap hF
  refine ⟨C, hC, fun φ hφ => ?_⟩
  rw [hDC φ hφ]
  refine setLIntegral_congr_fun (measurableSet_goodLoc r T T') ?_
  intro c hc
  obtain ⟨s₁, hs₁, s₁', hs₁', hcs⟩ :=
    h1 n r k ε e z z' T T' sc hF c hc (h0 c) (h c) (hh0 c hc) (hh c hc)
  beta_reduce
  congr 1
  rw [hcs]
  have eS := hR n r k ε e z z' T T' hF μS hμ s₁ hs₁
  have eS' := hR n r k ε e z' z T' T hF' μS' hμ' s₁' hs₁'
  symm
  exact inner_dc μS μS' s₁ s₁' (h0 c) eS eS' φ

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
