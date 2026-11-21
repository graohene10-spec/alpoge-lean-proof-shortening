import Formalism.GradedWeylDivisibility.StatementC

namespace Formalism.GradedWeylDivisibility

theorem standardMonomialSpanOf : StandardMonomialSpanOf := by
  exact fun h r n ν _ => h ℤ r n ν

end Formalism.GradedWeylDivisibility
