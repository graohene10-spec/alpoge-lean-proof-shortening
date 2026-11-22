import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.FlagMatLower
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.PtEntryNeZeroImp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.SuperdiagPairingAdjacent

open Matrix

noncomputable section

namespace PI.AmpRootCommon

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem pt_spec (p : Point ℂ (r + 1)) (i : Fin (r + 1)) :
    pv p.1 i.val < r + 1 ∧ pv p.1 (pv p.1 i.val) = i.val ∧ ptEntry p.1 i.val (pv p.1 i.val) ≠ 0 := by
  simpa only [p.2.2] using pv_spec p.1 p.2.1 i.val (by rw [p.2.2]; exact i.isLt)

def ptσ (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : Fin (r + 1) := ⟨pv p.1 i.val, (pt_spec p i).1⟩

def ptζ (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : ℂ :=
  (-1 : ℂ) ^ (r - (ptσ p i).val) * ptMat p i (ptσ p i)

theorem ptσ_invol (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : ptσ p (ptσ p i) = i := Fin.ext (pt_spec p i).2.1

theorem ptζ_ne (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : ptζ p i ≠ 0 := by
  unfold ptζ
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pt_spec p i).2.2

theorem neg_one_pow_mul_self (m : ℕ) : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by
  simp only [← mul_pow, neg_mul_neg, one_mul, one_pow]

theorem zhat_pt {z z' : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : Point ℂ (r + 1)} (hP : ZhatO k r z z' g = ptMat p) (i j : Fin (r + 1)) :
    Zhat k r z z' g i j = if j = ptσ p i then ptζ p i else 0 := by
  have hZ : Zhat k r z z' g i j = (-1 : ℂ) ^ (r - j.val) * ptMat p i j := by
    have h := congrFun (congrFun hP i) j
    simp only [ZhatO] at h
    rw [← h, ← mul_assoc, neg_one_pow_mul_self, one_mul]
  rw [hZ]
  split_ifs with hj
  · subst hj
    rfl
  · have : ptEntry p.1 i.val j.val = 0 := by
      by_contra hne
      exact hj (Fin.ext (ptEntry_ne_zero_imp p.1 i.val j.val hne))
    show (-1 : ℂ) ^ (r - j.val) * ptEntry p.1 i.val j.val = 0
    rw [this, mul_zero]

theorem pt_adj (p : Point ℂ (r + 1)) (i i1 : Fin (r + 1)) (hi1 : i1.val = i.val + 1) :
    ((ptσ p i1).val + 1 = (ptσ p i).val ∧ ptζ p (ptσ p i1) = - ptζ p (ptσ p i)) ∨
      (ptσ p i).val < (ptσ p i1).val := by
  rcases pv_adj p.1 p.2.1 i.val (by rw [p.2.2]; omega) with ⟨h1, h2⟩ | h1
  · left
    refine ⟨by simpa [ptσ, hi1] using h1, ?_⟩
    unfold ptζ
    rw [ptσ_invol p i1, ptσ_invol p i]
    show (-1 : ℂ) ^ (r - i1.val) * ptEntry p.1 (pv p.1 i1.val) i1.val =
      -((-1 : ℂ) ^ (r - i.val) * ptEntry p.1 (pv p.1 i.val) i.val)
    rw [hi1, h2]
    have hr : r - i.val = (r - (i.val + 1)) + 1 := by omega
    rw [hr, pow_succ]
    ring
  · right
    simpa [ptσ, hi1] using h1

theorem flag_rel_Rset {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    (hx : x ∈ Formalism.MainNotions.S.Rset k r g) :
    (flagMat k r z (g * x * g⁻¹))ᴴ * Zhat k r z z' g * flagMat k r z' x = Zhat k r z z' g := by
  have hxe : g⁻¹ * (g * x * g⁻¹) * g = x := by
    calc g⁻¹ * (g * x * g⁻¹) * g = (g⁻¹ * g) * x * (g⁻¹ * g) := by simp only [Matrix.mul_assoc]
      _ = x := by simp only [uh_inv_mul hg, Matrix.one_mul, Matrix.mul_one]
  have ha : g * x * g⁻¹ ∈ RStab k r g := ⟨hx.2, by rw [hxe]; exact hx.1⟩
  simpa only [hxe] using flag_rel hz hz' hg ha

section AtPt

variable {z z' : Fin (2 * r + k + 1) → ℂ} {g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
  {p : Point ℂ (r + 1)}

private theorem isUnit_det_of_unitriangular {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : u.BlockTriangular id)
    (hd : ∀ i, u i i = 1) : IsUnit u.det := by
  rw [Matrix.det_of_upperTriangular hu, Finset.prod_eq_one fun i _ => hd i]
  exact isUnit_one

theorem flag_entry (hz : inWb k r z) (hz' : inWb k r z') (hg : g ∈ UH (Hpk k r))
    (hP : ZhatO k r z z' g = ptMat p) (ha : a ∈ RStab k r g) (i j : Fin (r + 1)) :
    ptζ p i * flagMat k r z' (g⁻¹ * a * g) (ptσ p i) j =
      star ((flagMat k r z a)⁻¹ (ptσ p j) i) * ptζ p (ptσ p j) := by
  have hU := isUnit_det_of_unitriangular (flagMat k r z a) (flagMat_upper ha.1) (flagMat_diag ha.1)
  have hrel := flag_rel hz hz' hg ha
  have hkey : Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g) =
      ((flagMat k r z a)⁻¹)ᴴ * Zhat k r z z' g := by
    conv_rhs => rw [← hrel]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ hU, Matrix.conjTranspose_one, Matrix.one_mul]
  have hσ : ∀ l, (j = ptσ p l) ↔ (l = ptσ p j) := by
    intro l
    constructor <;> rintro rfl <;> exact (ptσ_invol p _).symm
  simpa only [Matrix.mul_apply, zhat_pt hP, hσ, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] using
    congrFun (congrFun hkey i) j

private theorem blockTriangular_inv_of_unitriangular {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : u.BlockTriangular id)
    (hd : ∀ i, u i i = 1) : u⁻¹.BlockTriangular id := by
  have hU := isUnit_det_of_unitriangular u hu hd
  letI : Invertible u := ⟨u⁻¹, Matrix.nonsing_inv_mul u hU, Matrix.mul_nonsing_inv u hU⟩
  exact Matrix.blockTriangular_inv_of_blockTriangular hu

private theorem star_flagMat_mul_ptZeta_eq (hz : inWb k r z) (hz' : inWb k r z') (hg : g ∈ UH (Hpk k r))
    (hP : ZhatO k r z z' g = ptMat p) (ha : a ∈ RStab k r g) (m n : Fin (r + 1)) :
    star (flagMat k r z a (ptσ p n) m) * ptζ p (ptσ p n) =
      ptζ p m * (flagMat k r z' (g⁻¹ * a * g))⁻¹ (ptσ p m) n := by
  have hx : g⁻¹ * a * g ∈ Nset k r := ha.2
  have hU := isUnit_det_of_unitriangular (flagMat k r z' (g⁻¹ * a * g)) (flagMat_upper hx) (flagMat_diag hx)
  have hrel := flag_rel hz hz' hg ha
  have hkey : (flagMat k r z a)ᴴ * Zhat k r z z' g =
      Zhat k r z z' g * (flagMat k r z' (g⁻¹ * a * g))⁻¹ := by
    rw [← Matrix.mul_one ((flagMat k r z a)ᴴ * Zhat k r z z' g),
      ← Matrix.mul_nonsing_inv _ hU, ← Matrix.mul_assoc, hrel]
  have hσ : ∀ l, (n = ptσ p l) ↔ (l = ptσ p n) := by
    intro l
    constructor <;> rintro rfl <;> exact (ptσ_invol p _).symm
  simpa only [Matrix.mul_apply, zhat_pt hP, hσ, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.conjTranspose_apply] using
    congrFun (congrFun hkey m) n

theorem flag_offblock (hz : inWb k r z) (hz' : inWb k r z') (hg : g ∈ UH (Hpk k r))
    (hP : ZhatO k r z z' g = ptMat p) (ha : a ∈ RStab k r g) (i j : Fin (r + 1))
    (hlt : (ptσ p i).val < (ptσ p j).val) :
    flagMat k r z' (g⁻¹ * a * g) i j = 0 ∧ flagMat k r z a i j = 0 := by
  have hlt' : ptσ p i < ptσ p j := hlt
  refine ⟨?_, ?_⟩
  · have h := flag_entry hz hz' hg hP ha (ptσ p i) j
    rw [ptσ_invol] at h
    have hv := blockTriangular_inv_of_unitriangular (flagMat k r z a) (flagMat_upper ha.1) (flagMat_diag ha.1)
    have h0 : (flagMat k r z a)⁻¹ (ptσ p j) (ptσ p i) = 0 := hv hlt'
    rw [h0, star_zero, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (ptζ_ne p _)
  · have h := star_flagMat_mul_ptZeta_eq hz hz' hg hP ha j (ptσ p i)
    rw [ptσ_invol] at h
    have hx : g⁻¹ * a * g ∈ Nset k r := ha.2
    have hv := blockTriangular_inv_of_unitriangular (flagMat k r z' (g⁻¹ * a * g)) (flagMat_upper hx) (flagMat_diag hx)
    have h0 : (flagMat k r z' (g⁻¹ * a * g))⁻¹ (ptσ p j) (ptσ p i) = 0 := hv hlt'
    rw [h0, mul_zero] at h
    exact star_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (ptζ_ne p i))

end AtPt

end PI.AmpRootCommon
