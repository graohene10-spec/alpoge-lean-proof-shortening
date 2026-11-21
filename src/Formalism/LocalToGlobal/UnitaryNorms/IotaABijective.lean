import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower

noncomputable section

namespace Formalism.L2.Host

theorem iota_mem (ι : Qb →+* ℂ) (x : Qb) : ι x ∈ algebraicClosure ℚ ℂ := by
  exact mem_algebraicClosure_iff.2 (((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).algHom ι.toRatAlgHom)

def iotaA (ι : Qb →+* ℂ) : Qb →+* algebraicClosure ℚ ℂ := ι.codRestrict (algebraicClosure ℚ ℂ) (iota_mem ι)

theorem iotaA_bijective (ι : Qb →+* ℂ) : Function.Bijective (iotaA ι) := by
  refine ⟨(iotaA ι).injective, fun y => ?_⟩
  have hy : IsIntegral ℚ y := IntermediateField.isIntegral_iff.2
    (mem_algebraicClosure_iff.1 y.2).isIntegral
  refine RingHom.mem_range.1 (Polynomial.Splits.mem_range_of_isRoot
    (IsAlgClosed.splits ((minpoly ℚ y).map (algebraMap ℚ Qb)))
    (Polynomial.map_ne_zero (f := algebraMap ℚ Qb) (minpoly.ne_zero hy)) ?_)
  rw [Polynomial.map_map, Subsingleton.elim ((iotaA ι).comp (algebraMap ℚ Qb))
    (algebraMap ℚ (algebraicClosure ℚ ℂ)), Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map,
    ← Polynomial.aeval_def]
  exact minpoly.aeval ℚ y

def algC (ι : Qb →+* ℂ) : Qb ≃+* algebraicClosure ℚ ℂ := RingEquiv.ofBijective (iotaA ι) (iotaA_bijective ι)

@[simp] theorem algC_coe (ι : Qb →+* ℂ) (x : Qb) : ((algC ι x : algebraicClosure ℚ ℂ) : ℂ) = ι x := rfl

end Formalism.L2.Host
