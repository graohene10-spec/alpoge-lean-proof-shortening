import Mathlib

noncomputable section

namespace PI.OrbShared

open MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

variable {σ τ υ R : Type*} [CommRing R]

theorem hasSubst_killCompl (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a) :
    HasSubst (fun s => killCompl e (a s)) where
  const_coeff s := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_killCompl, Finsupp.embDomain_zero,
      coeff_zero_eq_constantCoeff_apply]
    exact ha.const_coeff s
  coeff_zero d :=
    (ha.coeff_zero (Finsupp.embDomain e d)).subset fun s hs => by
      simpa [coeff_killCompl] using hs

theorem continuous_killCompl [UniformSpace R] [DiscreteUniformity R] (e : υ ↪ τ) :
    Continuous (killCompl (R := R) e : MvPowerSeries τ R → MvPowerSeries υ R) := by
  apply continuous_pi
  intro x
  have : (fun p : MvPowerSeries τ R => (killCompl e p) x) = fun p => coeff (Finsupp.embDomain e x) p := by
    funext p; exact coeff_killCompl p x
  rw [this]
  exact WithPiTopology.continuous_coeff R _

theorem killCompl_subst (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (f : MvPowerSeries σ R) :
    killCompl e (subst a f) = subst (fun s => killCompl e (a s)) f := by
  let _ : UniformSpace R := ⊥
  have _ : DiscreteUniformity R := ⟨rfl⟩
  have hb := hasSubst_killCompl e ha
  rw [comp_subst_apply ha (continuous_killCompl e) f, ← coe_substAlgHom hb, substAlgHom_eq_aeval]

theorem killCompl_eq_subst (e : υ ↪ τ) (f : MvPowerSeries τ R) :
    killCompl e f = subst (fun t => killCompl e (X t : MvPowerSeries τ R)) f := by
  simpa [subst_self] using killCompl_subst e (HasSubst.X (S := R) (σ := τ)) f

end PI.OrbShared
