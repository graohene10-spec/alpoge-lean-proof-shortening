import Formalism.GradedWeylDivisibility.StatementA

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem fischerInnerWeightOrthogonal_holds : FockWeightOrth := by
  intro σ M _ w μ μ' f g hne hf hg
  unfold Formalism.REAL.fockF
  refine Finset.sum_eq_zero fun m hm => ?_
  have hgm : g.coeff m = 0 := Classical.byContradiction fun h => hne ((hf (mem_support_iff.mp hm)).symm.trans (hg h))
  simp [hgm]

end Formalism.GradedWeylDivisibility
