import Formalism.SharpRestriction.GrowthBounds.RootWeights.SubstitutionPreservesOfGenerators

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem genericMatrixInverse_eq_adjugate (R : Type*) [CommRing R] (n : ℕ) :
    genericMatrixInverse R n = (IsLocalization.Away.invSelf (S := GLCoord R n) (genMat R n).det) •
      ((genMat R n).adjugate.map (algebraMap _ (GLCoord R n))) := by
  ext i j
  simp [genericMatrixInverse, Matrix.smul_apply]

theorem genericMatrixInverse_mul (R : Type*) [CommRing R] (n : ℕ) : genericMatrixInverse R n * genericMatrixRootWeights R n = 1 := by
  rw [genericMatrixInverse_eq_adjugate, genericMatrixRootWeights, Matrix.smul_mul, ← Matrix.map_mul, Matrix.adjugate_mul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_one, mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  · simp

theorem genericMatrix_mul_inverse (R : Type*) [CommRing R] (n : ℕ) : genericMatrixRootWeights R n * genericMatrixInverse R n = 1 := by
  rw [genericMatrixInverse_eq_adjugate, genericMatrixRootWeights, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_one, mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  · simp

section asm

variable {R : Type} [Field R] {ι : Type} [Fintype ι] (LL : Letters ι) {n : ℕ} (S : Set ι)

theorem generated_submodule_stable (G : MvPolynomial (ι × Fin n) R) (g : MvPolynomial (ι × Fin n) R →ₗ[R] MvPolynomial (ι × Fin n) R)
    (hg : g ∈ polUZgens R LL S) : ∀ x ∈ polGenSub R LL S G, g x ∈ polGenSub R LL S G := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    exact Submodule.subset_span ⟨g * u, Submonoid.mul_mem _ (Submonoid.subset_closure hg) hu, rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hy

theorem self_mem_generated_submodule (G : MvPolynomial (ι × Fin n) R) : G ∈ polGenSub R LL S G := Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩

theorem generic_translate_weights_mem (hT : TransvectionExpansion) (hTo : TorusActsThroughWeight) (hGr : BinomialStableContainsComponents) (G : MvPolynomial (ι × Fin n) R) :
    ∀ m ∈ (genericTranslate LL S G).support, wtS LL S m ∈ polWts LL S (polGenSub R LL S G) := by
  classical
  set W := polGenSub R LL S G with hWdef
  have hW2 : ∀ a k, ∀ x ∈ W, binomPol R LL S a k x ∈ W := fun a k x hx =>
    generated_submodule_stable LL S G (binomPol R LL S a k) (Or.inr ⟨a, k, rfl⟩) x hx
  have hWd : ∀ a b k, a ≠ b → ∀ x ∈ W, divPow R LL S a b k x ∈ W := fun a b k hab x hx =>
    generated_submodule_stable LL S G (divPow R LL S a b k) (Or.inl ⟨a, b, k, hab, rfl⟩) x hx
  haveI hdom : IsDomain (GLCoord R n) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Matrix.det_mvPolynomialX_ne_zero (Fin n) R : (genMat R n).det ≠ 0))
  let K := FractionRing (GLCoord R n)
  let ψ : GLCoord R n →+* K := algebraMap (GLCoord R n) K
  have hψ : Function.Injective ψ := IsFractionRing.injective (GLCoord R n) K
  let φ : R →+* K := ψ.comp (coefficientMap R n)
  set A : Matrix (Fin n) (Fin n) K := (genericMatrixInverse R n).map ψ with hAdef
  set A' : Matrix (Fin n) (Fin n) K := (genericMatrixRootWeights R n).map ψ with hA'def
  have hAA' : A * A' = 1 := by
    rw [hAdef, hA'def, ← Matrix.map_mul, genericMatrixInverse_mul, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have gA : SubstitutionPreservesExtension LL S φ W A A' :=
    substitution_preserves_extension_all LL S φ W hT hTo hGr hWd hW2 A A' hAA'
  have hGW : MvPolynomial.map φ G ∈ scalarExtension φ W := Submodule.subset_span ⟨G, self_mem_generated_submodule LL S G, rfl⟩
  have hHK : MvPolynomial.map ψ (genericTranslate LL S G) ∈ scalarExtension φ W := by
    rw [genericTranslate, map_matrixSubst, ← hAdef, ← hA'def, ← matrixSubst_map]
    exact gA _ hGW
  intro m hm
  have hsupp : m ∈ (MvPolynomial.map ψ (genericTranslate LL S G)).support := by
    rwa [MvPolynomial.support_map_of_injective _ hψ]
  exact scalarExtension_monomial_weights (LL := LL) (S := S) (φ := φ) (W := W) hGr hW2 _ hHK m hsupp

end asm

theorem generated_module_weight_lemma_of_interfaces (hT : TransvectionExpansion) (hTo : TorusActsThroughWeight) (hGr : BinomialStableContainsComponents) (hSt : TwistExponentsAreWeightEntries) (hSp : GenericMonomialsSpecialise) :
    GeneratedModuleWeightDescription := by
  intro R _ ι _ LL n _ S
  have coord_forall (G : MvPolynomial (ι × Fin n) R) (j : Fin n) (P : ℤ → Prop) :
      (∀ k ∈ sDegs LL S j G, P k) ↔
        (∀ μ ∈ polWts LL S (polGenSub R LL S G), P (μ j)) := by
    rw [hSt R ι LL n S j G]
    constructor
    · intro h
      exact weights_property_of_generic_translate (LL := LL) (S := S) (j := j) (Pr := P)
        hT hTo hSp G (fun m hm => h _ (Finset.mem_image_of_mem _ hm))
    · intro h k hk
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
      exact h _ (generic_translate_weights_mem LL S hT hTo hGr G m hm)
  refine ⟨fun G θ => ?_, fun G M => ?_⟩
  · rw [valS, Finset.le_inf_iff]
    simpa only [WithTop.coe_le_coe] using (coord_forall G (lastIdx n) (fun k => θ ≤ k))
  · rw [lam1S, Finset.sup_le_iff]
    simpa only [WithBot.coe_le_coe] using (coord_forall G (0 : Fin n) (fun k => k ≤ M))

end Formalism.MainNotions.G.GLWeightTheory
