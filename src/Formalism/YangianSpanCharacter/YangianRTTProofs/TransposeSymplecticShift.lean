import Formalism.YangianSpanCharacter.StatementT

namespace Formalism.YangianSpanCharacter.P

open Matrix

theorem transposeSymplecticShift : Formalism.YangianSpanCharacter.T.TJT := by
  intro R A _ _ _ p c ci Y h
  obtain ⟨h1, h2, h3⟩ := h
  have hpci : p * ci = ci * p - ci := by
    have hkey := congrArg (fun x => ci * x * ci) h3
    simp only [mul_add, add_mul, ← mul_assoc, h2, one_mul] at hkey
    simp only [mul_assoc, h1, mul_one] at hkey
    rw [hkey]; abel
  have hc : ∀ x : A, algebraMap R A Y * x = x * algebraMap R A Y := fun x => Algebra.commutes Y x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.J, map_add, add_mul, mul_add]
  all_goals first
    | exact h1
    | exact h2
    | (rw [hpci, hc ci]; abel)

theorem planeWaveIntertwining : Formalism.YangianSpanCharacter.T.PlaneWave := by
  intro R A _ _ _ p c ci f s Y hfc hfci hpf
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two]
  · have key : c * f * algebraMap R A s = algebraMap R A s * f * c := by
      rw [← hfc, mul_assoc, ← Algebra.commutes, ← mul_assoc]
      exact congrArg (· * c) (Algebra.commutes s f).symm
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two, hfc, hfci] <;>
      simp only [mul_add, add_mul, mul_neg, neg_mul, hpf, key, Algebra.commutes] <;>
      first | noncomm_ring | abel

theorem unipotentSymplectic : Formalism.YangianSpanCharacter.T.UJU := by
  intro R A _ _ _ s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]

theorem isWeylTripleShiftModel : Formalism.YangianSpanCharacter.T.WeylModel := by
  refine ⟨?_, ?_, ?_⟩
  all_goals refine LinearMap.ext fun f => funext fun n => ?_
  all_goals simp [Formalism.YangianSpanCharacter.T.cM, Formalism.YangianSpanCharacter.T.ciM, Formalism.YangianSpanCharacter.T.pM, LinearMap.funLeft_apply]
  all_goals try ring

end Formalism.YangianSpanCharacter.P
