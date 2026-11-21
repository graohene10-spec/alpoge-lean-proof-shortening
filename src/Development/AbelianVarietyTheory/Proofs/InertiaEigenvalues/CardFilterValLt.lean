import Mathlib

namespace GlobalTheory.CardFilterLt

theorem card_filter_val_lt : ∀ {n h : ℕ}, h ≤ n → Finset.card {m : Fin n | (↑m : ℕ) < h} = h := by
  intro n h hh
  have key : (Finset.univ.filter (fun m : Fin n => (m : ℕ) < h)).map Fin.valEmbedding
      = Finset.range h := by
    ext k
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact hm
    · intro hk
      exact ⟨⟨k, hk.trans_le hh⟩, hk, rfl⟩
  simpa using congrArg Finset.card key

end GlobalTheory.CardFilterLt
