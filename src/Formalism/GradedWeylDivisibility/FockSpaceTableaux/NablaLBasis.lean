import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem nablaLBasis_of (h : RowActMul) : NablaLBasis := by
  intro R K _ _ _ _ hinj k n ν ι b μ hb g hg
  have hinvA : ∀ A : Matrix (Fin k) (Fin k) K, IsUnit A.det → ∀ x : MvPolynomial (Fin k × Fin n) K,
      rowAct K A (rowAct K A⁻¹ x) = x ∧ rowAct K A⁻¹ (rowAct K A x) = x := fun A hA x =>
    ⟨ldlat_rowAct_inv_left h A hA x, ldlat_rowAct_inv_right h A hA x⟩
  have hφinj : Function.Injective (map (algebraMap R K) : MvPolynomial (Fin k × Fin n) R → _) :=
    MvPolynomial.map_injective _ hinj
  let L : MvPolynomial (Fin k × Fin n) R →ₗ[R] MvPolynomial (Fin k × Fin n) K :=
    ((rowAct K g⁻¹).toLinearMap.restrictScalars R).comp (mapAlgHom (Algebra.ofId R K)).toLinearMap
  have hL : ∀ p, L p = rowAct K g⁻¹ (map (algebraMap R K) p) := fun p => rfl
  have hLinj : Function.Injective L := by
    intro p q hpq
    rw [hL, hL] at hpq
    have e := congrArg (rowAct K g) hpq
    rw [(hinvA g hg _).1, (hinvA g hg _).1] at e
    exact hφinj e
  refine ⟨?_, ?_⟩
  · exact hb.1.map' L (LinearMap.ker_eq_bot.mpr hLinj)
  · have e1 : Set.range (fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) = L '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, hb.2.1]
    ext F
    unfold nablaL
    rw [Submodule.mem_map, Submodule.mem_comap, Submodule.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      show map (algebraMap R K) p = rowAct K g (L p)
      rw [hL, (hinvA g hg _).1]
    · rintro ⟨p, hp, hpF⟩
      refine ⟨p, hp, ?_⟩
      have e : map (algebraMap R K) p = rowAct K g F := hpF
      rw [hL, e, (hinvA g hg _).2]

end Formalism.GradedWeylDivisibility
