import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.Development

noncomputable section

namespace PI.SzEatI.W

open Formalism.BasicNotions Formalism.MainNotions.G

section basic

variable {D : D7} (L : SizeData₂ D)

theorem x_one_le : 1 ≤ L.sc.x := L.sc.one_lt_alt.le

theorem x_pos : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt

theorem b_pos : 0 < L.sc.b := Real.exp_pos _

theorem one_le_b : 1 ≤ L.sc.b := by
  simpa [Scale.b, Scale.L] using Real.one_le_exp (Real.rpow_nonneg (x_pos L).le _)

theorem a_pos : 0 < L.sc.a := mul_pos (x_pos L) (b_pos L)

theorem b'_pos : 0 < L.sc.b' := div_pos (a_pos L) (Real.exp_pos _)

theorem n_one_le : (1 : ℝ) ≤ (D.R.n : ℝ) := by
  exact_mod_cast D.R.ord_pos

theorem w''_nonneg : 0 ≤ L.sc.w'' D.R.n :=
  div_nonneg (b'_pos L).le (mul_nonneg (x_pos L).le (Nat.cast_nonneg _))

theorem w''_le_b' : L.sc.w'' D.R.n ≤ L.sc.b' :=
  div_le_self (b'_pos L).le (one_le_mul_of_one_le_of_one_le (x_one_le L) (n_one_le (D := D)))

theorem b'_div_x_le : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self (b'_pos L).le (x_one_le L)

theorem b'_div_x_nonneg : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (b'_pos L).le (x_pos L).le

theorem bT_le (hSz : Formalism.MainNotions.SizesAt L) (t : D.host.TT) : (L.bT t : ℝ) ≤ 2 * L.sc.b' := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -⟩ := hSz
  have hx := x_pos L
  have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg hx.le _) hLa.1
  set q := Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) with hq
  have h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / (D.R.k : ℝ) :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.log_nonneg (x_one_le L))) hLa0)
      (Nat.cast_nonneg _)
  have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (x_one_le L) (by norm_num)
  have h4 : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / (D.R.k : ℝ) = 4 * q := by
    rw [hq]; ring
  have hR := hRho
  unfold Formalism.MainNotions.SizeRho at hR
  rw [h4] at hR
  have hq1 : q ≤ 1 := by linarith
  have hB := hBot t
  have h5 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) = q * L.sc.b' := by
    rw [hq]; ring
  rw [h5] at hB
  have h6 : q * L.sc.b' ≤ L.sc.b' := mul_le_of_le_one_left (b'_pos L).le hq1
  linarith

end basic

theorem stepW : StepW := by
  intro D L hSz hbb j hj z
  unfold SizeData₂.lifts at hj
  obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.1 hj
  unfold wPl
  have hη := L.etaSz_pos
  have hb := b_pos L
  by_cases hth : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces
  · have hw := L.win_thick j hj1 hjm (tauPl D z) hth
    constructor <;> linarith [hw.1, hw.2]
  by_cases htop : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 htop
    have hw := L.win_top j hj1 hjm (tauPl D z) ⟨t, ht⟩ hte.symm
    constructor <;> linarith [hw.1, hw.2, bT_le L hSz ⟨t, ht⟩, L.bT_ge ⟨t, ht⟩,
      b'_div_x_le L, b'_div_x_nonneg L, (b'_pos L).le]
  · have hthin : D.host.IsThin (D.eTau (tauPl D z) : D.R.GG) :=
      ⟨(D.eTau (tauPl D z)).2, htop, hth⟩
    have hw := L.win_thin j hj1 hjm (tauPl D z) hthin
    constructor <;> linarith [hw.1, hw.2, w''_nonneg L, w''_le_b' L]

end PI.SzEatI.W
