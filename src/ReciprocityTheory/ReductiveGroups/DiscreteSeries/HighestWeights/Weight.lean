import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.SingleMulJmComm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex
import Formalism.RealPlaceAnalysis.QuotientSettingHolds

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem KType.kHighest_w {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.KHighest ε (kunits T) Λ T.w := ⟨fun a => T.w_wt a, fun a b hab he => T.w_hw a b hab he⟩

theorem KType.w_ne_zero {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.w ≠ 0 := by
  intro h
  simpa [h, norm_zero, zero_ne_one] using T.w_norm

theorem KType.kSpan_eq_top {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Formalism.REAL.kSpan ε (kunits T) T.w = ⊤ := by
  rcases KType.dτ_irred T (Formalism.REAL.kSpan ε (kunits T) T.w)
    (fun a b hab v hv => Formalism.REAL.compact_span_stable T.w a b hab v hv) with h | h
  · exfalso
    have hw := Formalism.REAL.mem_compact_span_self (ε := ε) (F := kunits T) T.w
    rw [h, Submodule.mem_bot] at hw
    exact (KType.w_ne_zero T) hw
  · exact h

theorem KType.hw_unique {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {ν : Fin n → ℝ} {v : T.V}
    (hv : v ≠ 0) (h : IsKHWVec ε (kunits T) ν v) : ν = Λ ∧ ∃ c : ℂ, v = c • T.w := by
  have hmem : v ∈ Formalism.REAL.kSpan ε (kunits T) T.w := by rw [KType.kSpan_eq_top T]; trivial
  rcases Formalism.REAL.kHiUniq T.V n ε (kunits T) Λ ν T.w v (KType.kRel T) (KType.kUnit T) (KType.kHighest_w T) hmem h with h0 | h1
  · exact absurd h0 hv
  · exact h1

theorem wtw_eq_sum (w : List (Fin n × Fin n)) :
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → (b, a) ∈ w) ∧
      -Formalism.REAL.wordWeightShift w = ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, fun a b h => absurd rfl h, by simp [Formalism.REAL.wordWeightShift]⟩
  | cons p w ih =>
    obtain ⟨c, hc, heq⟩ := ih
    refine ⟨fun a b => c a b + if a = p.2 ∧ b = p.1 then 1 else 0, ?_, ?_⟩
    · intro a b hab
      change c a b + (if a = p.2 ∧ b = p.1 then 1 else 0) ≠ 0 at hab
      by_cases h : a = p.2 ∧ b = p.1
      · obtain ⟨rfl, rfl⟩ := h
        simp
      · rw [if_neg h, add_zero] at hab
        exact List.mem_cons_of_mem _ (hc a b hab)
    · have hs : ∑ a, ∑ b, (((if a = p.2 ∧ b = p.1 then 1 else 0 : ℕ)) : ℝ) • root a b = root p.2 p.1 := by
        rw [Finset.sum_eq_single p.2, Finset.sum_eq_single p.1]
        · simp
        · intro b _ hb
          simp [hb]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · intro a _ ha
          simp [ha]
        · intro h
          exact absurd (Finset.mem_univ _) h
      simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib, hs, ← heq]
      simp only [Formalism.REAL.wordWeightShift, root]
      abel

theorem KType.weight_le {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {μ : Fin n → ℝ} {v : T.V}
    (hv : v ≠ 0) (hμ : ∀ a, T.dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v) :
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b ∧ ε a = ε b) ∧
      Λ - μ = ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  have hmem : v ∈ Formalism.REAL.lowSpan ε (kunits T) T.w := by
    rw [← Formalism.REAL.compact_span_eq_lowering (KType.kRel T) (KType.kHighest_w T), KType.kSpan_eq_top T]; trivial
  obtain ⟨w, hw, hwμ⟩ : ∃ w : List (Fin n × Fin n), (∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) ∧
      Λ + Formalism.REAL.wordWeightShift w = μ := by
    by_contra hne
    push Not at hne
    have horth : ∀ y ∈ Formalism.REAL.lowSpan ε (kunits T) T.w, inner ℂ v y = 0 := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro z ⟨w, hw, rfl⟩
        have hwt := Formalism.REAL.word_action_weight (KType.kRel T) (KType.kHighest_w T).1 w (fun q hq => (hw q hq).1)
        exact Formalism.REAL.kWtOrth T.V n ε (kunits T) μ _ v _ (KType.kUnit T) (fun a => hμ a) hwt
          (fun h => hne w hw h.symm)
      · simp
      · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx; rw [inner_smul_right, hx, mul_zero]
    exact hv (inner_self_eq_zero.mp (horth v hmem))
  obtain ⟨c, hc, he⟩ := wtw_eq_sum (n := n) w
  refine ⟨c, fun a b hab => ?_, ?_⟩
  · have := hw _ (hc a b hab)
    exact ⟨this.2, this.1.symm⟩
  · rw [← he, ← hwμ]; abel

end ReciprocityTheory.ChartRestriction.DS.HW
