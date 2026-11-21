import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.BesselExistenceUniformOfReduced

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

namespace BData

variable {X : BData}

theorem meas_mul : Measurable fun p : Formalism.QuantumDeterminants.Mt X.k X.r × Formalism.QuantumDeterminants.Mt X.k X.r =>
    Formalism.QuantumDeterminants.lmulM (Matrix.of p.1) p.2 := by
  unfold Formalism.QuantumDeterminants.lmulM
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact Finset.measurable_sum _ fun l _ => by fun_prop

variable (X) in

def SquareIntegrabilityBound (B : X.H → X.Vp) : Prop := ∀ χ, X.IsCut B χ → l2SG X.ν (X.Wf B χ) < ⊤

end BData

def BesselFinalFacts : Prop :=
  ∀ X : BData, X.Hyp → X.LowSmooth ∧ X.SmoothCyc ∧
    ∀ B : X.H → X.Vp, X.IsFun B → X.CutStep B ∧ X.SquareIntegrabilityBound B ∧ X.Repro B ∧ X.Exchange B

def LowProjAll : Prop := ∀ X : BData, X.Hyp → X.LowProj

end Formalism.MainNotions.LeviCoordinates

end
