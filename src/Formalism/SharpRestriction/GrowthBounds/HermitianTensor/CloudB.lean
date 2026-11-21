import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ProdMemHten
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.LastNeZero

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

private theorem sub_wtPQ_apply_eq_ite (mm ccl P Q : ℕ) (lam : Fin (mm + 1 + 1) → ℤ) (h0 : lam 0 = (P : ℤ) + ccl)
    (hl : lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl)) (i : Fin (mm + 1 + 1)) :
    (lam - wtPQ (mm + 1) P Q) i = if i = 0 then (ccl : ℤ) else if i = Fin.last (mm + 1) then -(ccl : ℤ) else lam i := by
  exact lo_apply (mm + 1) ccl P Q lam h0 hl i

private theorem antitone_sub_wtPQ (mm ccl P Q : ℕ) (lam : Fin (mm + 1 + 1) → ℤ) (hlam : Antitone lam)
    (h0 : lam 0 = (P : ℤ) + ccl) (hl : lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl))
    (hmid : ∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam i| ≤ ccl) :
    Antitone (lam - wtPQ (mm + 1) P Q) := by
  exact lo_anti (mm + 1) (by omega) ccl P Q lam hlam h0 hl hmid

theorem restCloudLat_of (h1 : CloudOne) (hCO : CartanOnto) (hIso : CloudIsoP) : RestCloudLat := by
  unfold RestCloudLat
  intro p n' R mm hmm TT a ccl aw bw lam0 A B hbase hdom hoff hAB hc H Hp ze lo lo' hH hHp hze hlo hlo'
  subst hH hHp hze hlo hlo'
  have hdomlo : IsDominant (lam0 - flatW (mm + 1) A B) := by
    intro s
    by_cases hs : s ∈ TT
    · have e : (lam0 - flatW (mm + 1) A B) s = lam0 s - wtPQ (mm + 1) (A ⟨s, hs⟩) (B ⟨s, hs⟩) := by
        rw [Pi.sub_apply, ← flatW_top (mm + 1) A B ⟨s, hs⟩]
      rw [e]
      obtain ⟨h0, hl, hmid⟩ := (hbase s).1 hs
      obtain ⟨hA, hB⟩ := hAB ⟨s, hs⟩
      exact antitone_sub_wtPQ mm ccl _ _ (lam0 s) (hdom s) (by rw [h0]; linarith) (by rw [hl]; linarith) hmid
    · have e : (lam0 - flatW (mm + 1) A B) s = lam0 s := by
        rw [Pi.sub_apply, flatW_off (mm + 1) A B s hs, sub_zero]
      rw [e]
      exact hdom s
  have hdomlo' : IsDominant (dualW (lam0 - flatW (mm + 1) A B)) := by
    intro s a' b' hab
    show -(lam0 - flatW (mm + 1) A B) s b'.rev ≤ -(lam0 - flatW (mm + 1) A B) s a'.rev
    exact neg_le_neg (hdomlo s (Fin.rev_le_rev.mpr hab))
  have hadd1 : ∀ s, lamAt (flatW (mm + 1) (fun s : TT => A s + 2 * ccl) fun s : TT => B s + 2 * ccl) s
      = lamAt (flatW (mm + 1) A B) s + lamAt (flatW (mm + 1) (fun _ : TT => 2 * ccl) fun _ : TT => 2 * ccl) s := by
    intro s
    rw [← lamAt_add']
    congr 1
    exact flatW_add (mm + 1) A B (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl)
  have hadd2 : ∀ s, lamAt lam0 s = lamAt (flatW (mm + 1) A B) s + lamAt (lam0 - flatW (mm + 1) A B) s := by
    intro s
    rw [lamAt_sub']
    ring
  have hdz : dualWt (0 : Fin (mm + 1 + 1) → ℤ) = 0 := by
    funext i
    simp [dualWt]
  have hpos : ∀ s, PosOK R (mm + 1) (lamAt lam0 s) (lamAt (flatW (mm + 1) A B) s)
      (lamAt (flatW (mm + 1) (fun s : TT => A s + 2 * ccl) fun s : TT => B s + 2 * ccl) s)
      (lamAt (flatW (mm + 1) (fun _ : TT => 2 * ccl) fun _ : TT => 2 * ccl) s)
      (lamAt (lam0 - flatW (mm + 1) A B) s) (lamAt (dualW (lam0 - flatW (mm + 1) A B)) s)
      (if s ∈ TT then weylDim mm (cloudAt lam0 s) else 1) (if s ∈ TT then ⌈kappaOneExponent p a (mm + 1)⌉₊ else 0) := by
    intro s
    by_cases hs : s ∈ TT
    · rw [if_pos hs, if_pos hs]
      exact posOK_at_top h1 R mm hmm TT a ccl aw bw lam0 A B hbase hdom hAB hc ⟨s, hs⟩
    · rw [if_neg hs, if_neg hs, lamAt_dualW, lamAt_sub', tn_lamAt_zero lam0 s (hoff s hs),
        lamAt_flat_off (mm + 1) A B s hs,
        lamAt_flat_off (mm + 1) (fun s : TT => A s + 2 * ccl) (fun s : TT => B s + 2 * ccl) s hs,
        lamAt_flat_off (mm + 1) (fun _ : TT => 2 * ccl) (fun _ : TT => 2 * ccl) s hs, sub_self, hdz]
      exact posOK_zero R (mm + 1)
  obtain ⟨mH, mU, abelian₂, hlat, hrest⟩ := cloudTen R (mm + 1) lam0 _ _ _ _ _ hdom (flatW_dom _ _ _)
    (flatW_dom _ _ _) (flatW_dom _ _ _) hdomlo hdomlo' hadd1 hadd2 _ _ hpos hCO hIso
  refine ⟨mH, mU, abelian₂, hlat, fun gs hgs => ?_⟩
  obtain ⟨nb, z0, sb, sb', ka, hnb, hka, hrest2⟩ := hrest gs hgs
  refine ⟨nb, z0, sb, sb', ka, ?_, ?_, hrest2⟩
  · have e : (∏ s : Fin n', (if s ∈ TT then weylDim mm (cloudAt lam0 s) else 1))
        = ∏ s : TT, weylDim mm (cloudAt lam0 ↑s) := by
      rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_coe_sort TT (fun s => weylDim mm (cloudAt lam0 s))]
    rw [dimCl, ← e, ← hnb]
    exact (Rat.cast_natCast nb).symm
  · intro b
    have hb := hka b
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul] at hb
    exact hb

end Formalism.MainNotions.flipOneThree.Pf

end
