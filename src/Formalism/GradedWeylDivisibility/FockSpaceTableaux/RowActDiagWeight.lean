import Formalism.GradedWeylDivisibility.StatementD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem row_action_diagonal_weight : RowActDiagWeight := by
  intro R _ k n t μ f hf
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (rowW k n) d = μ := hf (mem_support_iff.mp hd)
  have hp : (d.prod fun v e => t v.1 ^ e) = ∏ a, t a ^ μ a := by
    rw [ldrow_prod_rowDeg]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← hw, ldrow_weight_rowW]
  rw [ldrow_rowAct_diag_eq, aeval_monomial, ← hp, smul_eq_C_mul, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, map_finsuppProd, map_pow, MvPolynomial.algebraMap_eq]
  ring

end Formalism.GradedWeylDivisibility
