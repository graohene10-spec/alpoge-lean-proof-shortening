import Mathlib
import Formalism.PeriodIntegrals.CMTraceOnto
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMTraceSurjective.IsTrMulConjOfMem

theorem traceSurjective_holds : PI.CMTraceOnto := by
  exact PI.CMT.main
