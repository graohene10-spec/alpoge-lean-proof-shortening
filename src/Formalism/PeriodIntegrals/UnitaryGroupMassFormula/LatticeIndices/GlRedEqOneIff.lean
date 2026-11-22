import Mathlib

noncomputable section

namespace MassDataIdxRed

open Matrix

theorem isUnit_of_map {R S : Type} [CommRing R] [IsLocalRing R] [Field S] (π : R →+* S)
    (hπ : Function.Surjective π) (r : R) (h : IsUnit (π r)) : IsUnit r := by
  by_contra hr
  have hm : r ∈ RingHom.ker π := by
    rw [IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπ)]
    exact (IsLocalRing.mem_maximalIdeal r).2 hr
  exact not_isUnit_zero (RingHom.mem_ker.mp hm ▸ h)

def glRed {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (π : R →+* S) :
    GL ι R →* GL ι S :=
  Units.map (π.mapMatrix : Matrix ι ι R →+* Matrix ι ι S).toMonoidHom

theorem glRed_coe {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (π : R →+* S)
    (A : GL ι R) : ((glRed π A : GL ι S) : Matrix ι ι S) = (A : Matrix ι ι R).map π := rfl

theorem glRed_surjective {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hloc : ∀ r, IsUnit (π r) → IsUnit r) :
    Function.Surjective (glRed (ι := ι) π) := by
  intro B
  choose f hf using hπ
  set A0 : Matrix ι ι R := (B : Matrix ι ι S).map f with hA0def
  have hA0 : A0.map π = (B : Matrix ι ι S) := by
    ext i j; simp [A0, hf]
  have hdet : IsUnit A0.det := by
    apply hloc
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA0]
    exact (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  refine ⟨Matrix.nonsingInvUnit A0 hdet, ?_⟩
  apply Units.ext
  rw [glRed_coe]
  exact hA0

theorem glRed_eq_one_iff {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (π : R →+* S) (A : GL ι R) :
    glRed π A = 1 ↔ ∀ i j, ((A : Matrix ι ι R) - 1) i j ∈ RingHom.ker π := by
  rw [← Units.val_inj, glRed_coe, Units.val_one]
  constructor
  · intro h i j
    simpa [RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply,
      Matrix.one_apply] using congrFun (congrFun h i) j
  · intro h
    ext i j
    simpa [RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply,
      Matrix.one_apply] using h i j

end MassDataIdxRed
