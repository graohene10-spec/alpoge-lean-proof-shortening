import Mathlib

noncomputable def UpperTheory.Reformulated.B.PairedCharacterCondition.TrScale :
    Prop :=
    ∀ (K : Type) [inst : Field K] [NumberField K] (V : Type) [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
      (M : Submodule (NumberField.RingOfIntegers K) V),
      Submodule.span K (↑M : Set V) = ⊤ → ∀ (f : V), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ (↑m : K) • f ∈ M

theorem UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale :
    UpperTheory.Reformulated.B.PairedCharacterCondition.TrScale := by
  intro K _ _ V _ _ _ _ M hM f
  have key : ∀ (c : K), IsIntegral ℤ c → ∀ x ∈ M, c • x ∈ M := by
    intro c hc x hx
    obtain ⟨r, rfl⟩ : ∃ r : NumberField.RingOfIntegers K, algebraMap _ K r = c := ⟨⟨c, hc⟩, rfl⟩
    simpa [algebraMap_smul] using M.smul_mem r hx
  have hint : ∀ n : ℤ, IsIntegral ℤ (n : K) := fun n => isIntegral_algebraMap (R := ℤ) (x := n)
  have hf : f ∈ Submodule.span K (↑M : Set V) := hM ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    simpa [smul_add, smul_smul, Int.cast_mul, mul_comm (b : K)] using
      M.add_mem (key _ (hint b) _ hx) (key _ (hint a) _ hy)
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    have halg : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨b, hb, hc⟩ := halg.exists_integral_multiple
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    simpa [smul_smul, Int.cast_mul, zsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      key _ hc _ hx
