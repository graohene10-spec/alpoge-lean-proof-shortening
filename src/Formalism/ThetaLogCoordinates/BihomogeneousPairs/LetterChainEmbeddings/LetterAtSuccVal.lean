import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.SmulMemOfNorm

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section block
variable {N r : ℕ} (D : BlockData N)

def wv (i : Fin D.T.t) (c : Fin r) : BVar N r D.T.t := Sum.inl (finPos N (D.T.pos i), c)
def ev (i : Fin D.T.t) (c : Fin r) : BVar N r D.T.t := Sum.inl (finPos N (D.T.pos i + 1), c)
def zi (r : ℕ) (i : Fin D.T.t) : BVar N r D.T.t := scalZ N r D.T.t (Fin.castSucc i)
def si (r : ℕ) (i : Fin D.T.t) : BVar N r D.T.t := scalS N r D.T.t (Fin.castSucc i)
def wU (c : Fin r) : BVar N r D.T.t := Sum.inl (Fin.castSucc D.uPos, c)
def zP (r : ℕ) : BVar N r D.T.t := scalZ N r D.T.t (Fin.last D.T.t)
def sP (r : ℕ) : BVar N r D.T.t := scalS N r D.T.t (Fin.last D.T.t)

variable {D}

theorem pos_succ_lt (hB : D.BlockOK) (i : Fin D.T.t) : D.T.pos i + 1 + 1 < N := by
  obtain ⟨_, h2, _, h4⟩ := hB
  have := h2 i
  omega

theorem finPos_pos_val (hB : D.BlockOK) (i : Fin D.T.t) : (finPos N (D.T.pos i)).val = D.T.pos i := by
  have := pos_succ_lt hB i
  exact min_eq_left (by omega)

theorem finPos_succ_val (hB : D.BlockOK) (i : Fin D.T.t) :
    (finPos N (D.T.pos i + 1)).val = D.T.pos i + 1 := by
  have := pos_succ_lt hB i
  exact min_eq_left (by omega)

theorem letterAt_pos_val (hB : D.BlockOK) (i : Fin D.T.t) : (D.letterAt (D.T.pos i)).val = D.T.pos i := by
  have := pos_succ_lt hB i
  exact min_eq_left (by omega)

theorem letterAt_succ_val (hB : D.BlockOK) (i : Fin D.T.t) :
    (D.letterAt (D.T.pos i + 1)).val = D.T.pos i + 1 := by
  have := pos_succ_lt hB i
  exact min_eq_left (by omega)

theorem pos_inj (hB : D.BlockOK) {i i' : Fin D.T.t} (h : D.T.pos i = D.T.pos i') : i = i' := hB.1.1.injective h

theorem pos_ne_succ (hB : D.BlockOK) (i i' : Fin D.T.t) : D.T.pos i ≠ D.T.pos i' + 1 := by
  intro h
  obtain ⟨hi, hti, _⟩ := hB.1.2.1 i
  obtain ⟨hi', _, hfi'⟩ := hB.1.2.1 i'
  have e : D.LL.vec ⟨D.T.pos i, by omega⟩ = D.LL.vec ⟨D.T.pos i' + 1, hi'⟩ := congrArg D.LL.vec (Fin.ext h)
  rw [hti, hfi'] at e
  exact absurd e (by decide)

theorem pos_lt_u (hB : D.BlockOK) (i : Fin D.T.t) : D.T.pos i + 1 < (D.uPos : ℕ) := hB.2.1 i

private theorem deg_lettersAt_of_pair (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (i : Fin D.T.t) (p : Fin N) (hp : p.val = D.T.pos i ∨ p.val = D.T.pos i + 1) :
    (D.lettersAt j jp).deg p = D.LL.deg p - j i := by
  simp only [BlockData.lettersAt]
  have hs : (∑ i', if p.val = D.T.pos i' ∨ p.val = D.T.pos i' + 1 then j i' else 0) = j i := by
    rw [Finset.sum_eq_single i]
    · rw [if_pos hp]
    · intro b _ hb
      rw [if_neg]
      rintro (hb₀ | hb₁) <;> rcases hp with hi₀ | hi₁
      · exact hb (pos_inj hB (hb₀.symm.trans hi₀))
      · exact pos_ne_succ hB b i (hb₀.symm.trans hi₁)
      · exact pos_ne_succ hB i b (hi₀.symm.trans hb₁)
      · exact hb (pos_inj hB (Nat.add_right_cancel (hb₁.symm.trans hi₁)))
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hu : p ≠ D.uPos := by
    intro h
    have hval := congrArg Fin.val h
    have hlt := pos_lt_u hB i
    rcases hp with hp | hp <;> omega
  rw [hs, if_neg hu, Nat.sub_zero]

theorem deg_lettersAt_pos (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i)) = D.LL.deg (D.letterAt (D.T.pos i)) - j i := by
  exact deg_lettersAt_of_pair hB j jp i (D.letterAt (D.T.pos i)) (Or.inl (letterAt_pos_val hB i))

theorem deg_lettersAt_pos_succ (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)) = D.LL.deg (D.letterAt (D.T.pos i + 1)) - j i := by
  exact deg_lettersAt_of_pair hB j jp i (D.letterAt (D.T.pos i + 1))
    (Or.inr (letterAt_succ_val hB i))

theorem deg_U (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    (D.lettersAt j jp).deg D.uPos = D.LL.deg D.uPos - jp := by
  simp only [BlockData.lettersAt]
  rw [Finset.sum_eq_zero (fun b _ => by
      rw [if_neg]
      have := pos_lt_u hB b
      omega)]
  simp

end block

end Formalism.InvariantFactorPaths.KP.LL
