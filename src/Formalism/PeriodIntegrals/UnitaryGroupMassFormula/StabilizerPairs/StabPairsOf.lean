import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConverseStep

open Matrix

noncomputable section

namespace PI.StabPairsW

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

theorem stabPairs_of (h1 : MapsStep) (h2 : PairFormula) (h3 : ConverseStep) (h4 : CompDet) :
    Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree := by
  intro k r z z' γ hs hp
  have hinj : ∀ ρ1 ∈ Rst k r z z' γ, ∀ ρ2 ∈ Rst k r z z' γ,
      pairMap k r z z' γ ρ1 = pairMap k r z z' γ ρ2 → ρ1 = ρ2 := by
    intro ρ1 h1' ρ2 h2' heq
    rw [h2 k r z z' γ hs hp ρ1 h1', h2 k r z z' γ hs hp ρ2 h2', heq]
  refine ⟨⟨fun ρ hρ => h1 k r z z' γ hs hp ρ hρ, hinj,
    fun p hp' => ⟨rhoOf k r z z' γ p.1 p.2, (h3 k r z z' γ hs hp p hp').1,
      (h3 k r z z' γ hs hp p hp').2⟩⟩, ?_, ?_⟩
  · intro ρ1 h1' ρ2 h2' heq
    exact hinj ρ1 h1' ρ2 h2'
      ((h4 k r z z' γ hs hp _ (h1 k r z z' γ hs hp ρ1 h1') _
        (h1 k r z z' γ hs hp ρ2 h2')).1 heq)
  · intro ρ1 h1' ρ2 h2' heq
    exact hinj ρ1 h1' ρ2 h2'
      ((h4 k r z z' γ hs hp _ (h1 k r z z' γ hs hp ρ1 h1') _
        (h1 k r z z' γ hs hp ρ2 h2')).2 heq)

end PI.StabPairsW
