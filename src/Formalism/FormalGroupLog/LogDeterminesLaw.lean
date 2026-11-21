import Formalism.FormalGroupLog.FormalGroupLogProofs.HomPsSubstMvSubst
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

namespace Formalism.G

private lemma constantCoeff_powerSeries_subst_eq_zero' {R : Type*} [CommRing R] {τ : Type*} {a : MvPowerSeries τ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (p : PowerSeries R)
    (hp : PowerSeries.constantCoeff p = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a p) = 0 := by
  exact PowerSeries.constantCoeff_subst_eq_zero ha p hp

private lemma mvPowerSeries_subst_powerSeries_subst_eq_subst_subst {R : Type*} [CommRing R] {σ τ : Type*} {a : σ → MvPowerSeries τ R}
    (ha : MvPowerSeries.HasSubst a) {b : MvPowerSeries σ R} (hb : PowerSeries.HasSubst b)
    (p : PowerSeries R) :
    MvPowerSeries.subst a (PowerSeries.subst b p) = PowerSeries.subst (MvPowerSeries.subst a b) p :=
  MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const hb) ha p

theorem homComp : HomComp := by
  exact homComp_statement
theorem logIffHomGa : LogIffHomGa := by
  exact log_iff_hom_additive
theorem substInjective : SubstInjective := substInjective_statement
theorem isCommOfRat : IsCommOfRat := is_comm_of_rat

end Formalism.G
