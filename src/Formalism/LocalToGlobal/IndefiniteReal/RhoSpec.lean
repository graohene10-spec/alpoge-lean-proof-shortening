import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.InBlock
import Formalism.LocalToGlobal.IndefiniteReal.CxPassRep

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

namespace PassRep3

open Formalism.IndefR.CxPass.PassRep

section Lev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

private lemma exists_toF_bot_eq_toF (B : BlockDat K G Pl0) (Xs : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
    (Z : Submodule K B.S.Forms) (x : Fin (B.dZ ⟨Xs, P, ψ⟩ Z) → K) :
    ∃ y : Fin (B.dZ ⟨Xs, ⊥, 1⟩ Z) → K, B.toF ⟨Xs, ⊥, 1⟩ Z y = B.toF ⟨Xs, P, ψ⟩ Z x := by
  exact PassRep.toF_sub B Xs P ψ Z x

theorem sub_lvl (b : Bool) (t : I.A3.fam3.base3.Tup)
    (x : Fin ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ t) → K) :
    ∃ y, I.cg.toR I.X.zs false t y = I.cr.toR I.X.zs b t x := by
  cases b
  · exact exists_toF_bot_eq_toF (I.A.fam.R t) I.A.fam.X I.P0 I.ψ0 (I.X.zs.Z t) x
  · exact exists_toF_bot_eq_toF (I.A.fam.R t) I.A.fam.X I.P1 I.ψ1 (I.X.zs.Z t) x

private lemma cpt_injective' (σ : K →+* ℂ) {n : ℕ} {x y : Fin n → K} (h : cpt σ x = cpt σ y) : x = y :=
  funext fun i => σ.injective (congrFun h i)

theorem jt_spec (h2g : PrincipalLevelBijectivity I.A3 I.X (P1 := I.P1) (ψ1 := I.ψ1) (Dc := I.Dc) (Sp := I.Sp) (Zsc := I.Zsc)) (b : Bool) (t : I.A3.fam3.base3.Tup) :
    (∀ x, I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding ((I.Jt b t).mulVec x)) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x)) ∧
    ∀ x, I.cg.toR I.X.zs false t ((I.Jt b t).mulVec x) = I.cr.toR I.X.zs b t x := by
  have hg : ∀ x, ∃ y, I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding y) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x) := by
    intro x
    obtain ⟨y, hy⟩ := PassRep3.sub_lvl I b t x
    exact ⟨y, by rw [CxData.iC_cpt', CxData.iC_cpt', hy]⟩
  have hR := PassRep.relK I.A3.fam3.base3.v0.embedding (I.X.iC I.cg false t) (I.X.iC I.cr b t) (h2g.2 t).1 hg
  refine ⟨hR.2, fun x => ?_⟩
  obtain ⟨y, hy⟩ := PassRep3.sub_lvl I b t x
  have h1 : I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding y) =
      I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding ((I.Jt b t).mulVec x)) := by
    rw [show I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding ((I.Jt b t).mulVec x)) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x) from hR.2 x, CxData.iC_cpt', CxData.iC_cpt', hy]
  have h2 := cpt_injective' _ ((h2g.2 t).1 h1)
  rw [← h2, hy]

theorem rho_y {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    ∃ y : Fin I.Sg.D → K, I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 y =
      (I.A.fam.R I.A3.fam3.base3.μ0).r g (I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 x) := by
  exact PassRep.toF_act (I.A.fam.R I.A3.fam3.base3.μ0) I.A.fam.X H.ok.ok2.irr
    (I.X.zs.Z I.A3.fam3.base3.μ0) g
    (fun f hf => H.stable.1 _ (Sum.inr g) (Submodule.mem_map_of_mem hf)) x

theorem iCg_of_y {s : ℕ} (H : I.Hyp s) (g : G) (x y : Fin I.Sg.D → K)
    (hy : I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 y =
      (I.A.fam.R I.A3.fam3.base3.μ0).r g (I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 x)) :
    I.iCg (cpt I.A3.fam3.base3.v0.embedding y) = I.gE g (I.iCg (cpt I.A3.fam3.base3.v0.embedding x)) := by
  show I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) =
    I.gE g (I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x))
  erw [CxData.iC_cpt', CxData.iC_cpt', hy]
  exact H.gequiv _ g _

theorem rho_spec {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    I.iCg (cpt I.A3.fam3.base3.v0.embedding ((I.ρf g).mulVec x)) =
      I.gE g (I.iCg (cpt I.A3.fam3.base3.v0.embedding x)) := by
  have hg : ∀ x : Fin I.Sg.D → K, ∃ y : Fin I.Sg.D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding y) =
      ((I.gE g).comp I.iCg) (cpt I.A3.fam3.base3.v0.embedding x) := by
    intro x
    obtain ⟨y, hy⟩ := PassRep3.rho_y I H g x
    exact ⟨y, PassRep3.iCg_of_y I H g x y hy⟩
  exact (PassRep.relK I.A3.fam3.base3.v0.embedding I.iCg ((I.gE g).comp I.iCg) H.h2g.1 hg).2 x

theorem rho_cv {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) ((I.ρf g).mulVec x) =
      ((I.A.fam.R I.A3.fam3.base3.μ0).S.actMat (I.A.fam.R I.A3.fam3.base3.μ0).r g).mulVec
        (cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) x) := by
  obtain ⟨y, hy⟩ := PassRep3.rho_y I H g x
  have hyeq : y = (I.ρf g).mulVec x :=
    cpt_injective' _ (H.h2g.1 ((PassRep3.iCg_of_y I H g x y hy).trans (PassRep3.rho_spec I H g x).symm))
  subst hyeq
  have key : ∀ v : Fin I.Sg.D → K,
      cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) v =
      (I.A.fam.R I.A3.fam3.base3.μ0).S.basis.equivFun (I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 v) := by
    intro v
    show _ = (I.A.fam.R I.A3.fam3.base3.μ0).S.basis.equivFun
      ((I.A.fam.R I.A3.fam3.base3.μ0).toF ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) v)
    erw [BlockDat.toF_apply, LinearEquiv.apply_symm_apply]
    rfl
  rw [key, key, hy]
  first
  | exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm
  | (simp only [Basis.equivFun_apply]; exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm)
  | (simp only [Basis.equivFun_apply, CSD.actMat]; exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm)

theorem cv_epM {s : ℕ} (H : I.Hyp s) (P : Subgroup G) (ψ : P →* Kˣ) (y : Fin I.Sg.D → K) :
    cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) ((I.epM P ψ).mulVec y) =
      ((I.A.fam.R I.A3.fam3.base3.μ0).S.gaMat (I.A.fam.R I.A3.fam3.base3.μ0).r (lvlIdem P ψ)).mulVec
        (cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) y) := by
  exact PassRep.cv_typeProj (I.A.fam.R I.A3.fam3.base3.μ0) I.A.fam.X
    (I.X.zs.Z I.A3.fam3.base3.μ0) I.ρf (PassRep3.rho_cv I H) P ψ y

end Lev

end PassRep3

namespace In3

open Formalism.IndefR.CxPass.PassRep Formalism.IndefR.CxPass.PassRep3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

private theorem iCg_cpt_Jm_mulVec_and_Jm_injective {s : ℕ} (H : I.Hyp s) (b : Bool) :
    (∀ x : Fin (I.Sb b).D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ x)) =
      I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x)) ∧ Function.Injective (I.Jm b).mulVec := by
  have hg : ∀ x : Fin (I.Sb b).D → K, ∃ y : Fin I.Sg.D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding y) =
      I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x) := by
    intro x
    obtain ⟨y, hy⟩ := PassRep3.sub_lvl I b I.A3.fam3.base3.μ0 x
    refine ⟨y, ?_⟩
    show I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) = _
    erw [CxData.iC_cpt', CxData.iC_cpt', hy]
  have hR := PassRep.relK I.A3.fam3.base3.v0.embedding I.iCg (I.X.iC I.cr b I.A3.fam3.base3.μ0) H.h2g.1 hg
  refine ⟨hR.2, fun x y hxy => ?_⟩
  have h1 : I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x) =
      I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) :=
    (hR.2 x).symm.trans ((congrArg (fun v => I.iCg (cpt I.A3.fam3.base3.v0.embedding v)) hxy).trans (hR.2 y))
  exact PassRep3.cpt_injective' _ ((H.h2 b).1 h1)

theorem pJt : I.PJt := by
  intro s H b t
  obtain ⟨h1, h2⟩ := PassRep3.jt_spec I H.h2g b t
  refine ⟨h1, h2, fun x => ?_⟩
  have e1 : I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ (I.X.rowMat I.cr b t *ᵥ x))) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x) :=
    ((iCg_cpt_Jm_mulVec_and_Jm_injective I H b).1 _).trans (PassRep.key_row' I.X I.cr b (fun t => ((H.h2 b).2.1 t).2) (H.ratMu b) t x)
  have e2 : I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ x))) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x) :=
    (PassRep.key_row' I.X I.cg false (fun t => (H.h2g.2 t).2) H.ratMug t _).trans (h1 x)
  exact PassRep3.cpt_injective' _ (H.h2g.1 (e1.trans e2.symm))

theorem pRho : I.PRho := by
  intro s H
  have hsp := fun g x => PassRep3.rho_spec I H g x
  have hinj : ∀ M N : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K,
      (∀ x, I.iCg (cpt I.A3.fam3.base3.v0.embedding (M *ᵥ x)) = I.iCg (cpt I.A3.fam3.base3.v0.embedding (N *ᵥ x))) →
      M = N := by
    intro M N h
    have h' : ∀ x, M *ᵥ x = N *ᵥ x := fun x => PassRep3.cpt_injective' _ (H.h2g.1 (h x))
    exact Matrix.toLin'.injective (LinearMap.ext h')
  refine ⟨hinj _ _ fun x => ?_, fun g h => hinj _ _ fun x => ?_, hsp⟩
  · erw [hsp, Matrix.one_mulVec, map_one]
    rfl
  · erw [hsp, ← Matrix.mulVec_mulVec, hsp, hsp, map_mul]
    rfl

theorem pJ : I.PJ := by
  exact fun s H b => iCg_cpt_Jm_mulVec_and_Jm_injective I H b

theorem pRange : I.PRange := by
  intro s H b
  have hX := H.ok.ok2.irr
  have hJt : ∀ x, I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 (I.Jm b *ᵥ x) =
      I.cr.toR I.X.zs b I.A3.fam3.base3.μ0 x := by
    intro x
    obtain ⟨y, hy⟩ := PassRep3.sub_lvl I b I.A3.fam3.base3.μ0 x
    have h1 : I.iCg (cpt I.A3.fam3.base3.v0.embedding y) = I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ x)) := by
      rw [(iCg_cpt_Jm_mulVec_and_Jm_injective I H b).1 x]
      show I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) = _
      erw [CxData.iC_cpt', CxData.iC_cpt', hy]
    have h2 := PassRep3.cpt_injective' _ (H.h2g.1 h1)
    rw [← h2, hy]
  have key : ∀ (ℓ : Lvl K G) (v : Fin ((I.A.fam.R I.A3.fam3.base3.μ0).dZ ℓ (I.X.zs.Z I.A3.fam3.base3.μ0)) → K),
      cv (I.A.fam.R I.A3.fam3.base3.μ0) ℓ (I.X.zs.Z I.A3.fam3.base3.μ0) v =
        (I.A.fam.R I.A3.fam3.base3.μ0).S.basis.equivFun
          ((I.A.fam.R I.A3.fam3.base3.μ0).toF ℓ (I.X.zs.Z I.A3.fam3.base3.μ0) v) := by
    intro ℓ v
    erw [BlockDat.toF_apply, LinearEquiv.apply_symm_apply]
    rfl
  cases b
  · refine PassRep.range_eq_block (I.A.fam.R I.A3.fam3.base3.μ0) I.A.fam.X hX I.P0 I.ψ0 (I.X.zs.Z I.A3.fam3.base3.μ0) (I.Jm false) (fun x => ?_)
      (I.epM I.P0 I.ψ0) (fun y => PassRep3.cv_epM I H I.P0 I.ψ0 y)
    rw [key, key]
    exact congrArg _ (hJt x)
  · refine PassRep.range_eq_block (I.A.fam.R I.A3.fam3.base3.μ0) I.A.fam.X hX I.P1 I.ψ1 (I.X.zs.Z I.A3.fam3.base3.μ0) (I.Jm true) (fun x => ?_)
      (I.epM I.P1 I.ψ1) (fun y => PassRep3.cv_epM I H I.P1 I.ψ1 y)
    rw [key, key]
    exact congrArg _ (hJt x)

end In3

end Formalism.IndefR.CxPass
