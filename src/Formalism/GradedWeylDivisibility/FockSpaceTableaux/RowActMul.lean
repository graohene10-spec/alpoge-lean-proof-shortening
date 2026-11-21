import Formalism.GradedWeylDivisibility.StatementD

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem row_action_mul : RowActMul := by
  intro R _ k n g h
  refine MvPolynomial.algHom_ext fun v => ?_
  simp only [AlgHom.comp_apply, rowAct, aeval_X, map_sum, map_mul, aeval_C, Matrix.mul_apply,
    MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end Formalism.GradedWeylDivisibility
