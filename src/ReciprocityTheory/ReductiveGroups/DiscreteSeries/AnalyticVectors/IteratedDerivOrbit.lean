import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem norm_orbit_apply (hσ : IsURepOn (UJset ε) σ) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (t : ℝ) (w : H) : ‖σ (NormedSpace.exp ((t : ℂ) • X)) w‖ = ‖w‖ :=
  hσ.2.1 _ (exp_smul_mem_UJset hX t) w

theorem hasDerivAt_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (t : ℝ) :
    HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H))
      (σ (NormedSpace.exp ((t : ℂ) • X)) ((actM E X v : D) : H)) t := by
  have key : (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) =
      fun s : ℝ => σ (NormedSpace.exp ((t : ℂ) • X))
        (σ (NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) (v : H)) := by
    funext s
    have hs : (s : ℂ) = ((t + (s - t) : ℝ) : ℂ) := by
      rw [show t + (s - t) = s by ring]
    rw [hs, exp_add_smul X t (s - t),
      hσ.1.2 _ (exp_smul_mem_UJset hX t) _ (exp_smul_mem_UJset hX (s - t))]
    rfl
  rw [key]
  have h1 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hD.deriv X hX v)
  exact ((σ (NormedSpace.exp ((t : ℂ) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1

theorem iteratedDeriv_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (m : ℕ) :
    iteratedDeriv m (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) =
      fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) ((((actM E X) ^ m) v : D) : H) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [(hasDerivAt_orbit hσ hD hX ((actM E X ^ m) v) t).deriv, pow_succ', Module.End.mul_apply]

theorem contDiff_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (N : ℕ) :
    ContDiff ℝ N (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) := by
  refine contDiff_of_differentiable_iteratedDeriv (fun m _ => ?_)
  rw [iteratedDeriv_orbit hσ hD hX v m]
  exact fun t => (hasDerivAt_orbit hσ hD hX ((actM E X ^ m) v) t).differentiableAt

end Rep

end ReciprocityTheory.ChartRestriction.DS
