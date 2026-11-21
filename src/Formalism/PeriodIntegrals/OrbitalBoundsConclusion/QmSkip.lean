import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SkipSuccessorIndex.SkipSucc2

theorem quantum_minor_skip : PI.QmSkip := by
  exact ⟨PI.QmSkipWork.skipSucc, PI.QmSkipWork.skipSucc2⟩
