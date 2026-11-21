import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk34.MM :
    Nat → Nat → Type :=
    fun (P Q : Nat) ↦ Matrix (Sum (Fin P) (Fin Q)) (Sum (Fin P) (Fin Q)) Complex

theorem UpperTheory.Reformulated.B.Qk34.norm_le_sum :
    ∀ (P Q : Nat) (X : UpperTheory.Reformulated.B.Qk34.MM P Q),
      @LE.le Real Real.instLE
        (@Norm.norm (UpperTheory.Reformulated.B.Qk34.MM P Q)
          (@NormedRing.toNorm (UpperTheory.Reformulated.B.Qk34.MM P Q)
            (@Matrix.linftyOpNormedRing (Sum (Fin P) (Fin Q)) Complex
              (@instFintypeSum (Fin P) (Fin Q) (Fin.fintype P) (Fin.fintype Q))
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              fun (a b : Sum (Fin P) (Fin Q)) ↦
              @instDecidableEqSum (Fin P) (Fin Q) (instDecidableEqFin P) (instDecidableEqFin Q) a b))
          X)
        (∑ i : Sum (Fin P) (Fin Q), ∑ j : Sum (Fin P) (Fin Q), @Norm.norm Complex Complex.instNorm (X i j)) := by
  intro P Q X
  rw [Matrix.linfty_opNorm_def (A := X)]
  simpa only [NNReal.coe_sum, coe_nnnorm] using
    NNReal.coe_le_coe.mpr (Finset.sup_le fun i _ =>
      Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖₊)
        (fun _ _ => by positivity) (Finset.mem_univ i))
