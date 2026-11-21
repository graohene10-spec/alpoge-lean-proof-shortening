import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementG

namespace Formalism.InvariantFactorPaths.PW

open MvPolynomial Finset Formalism.GM.M Formalism.GM

theorem setTies_deg_le {N : ℕ} (LL : Letters N) (T : TieData) (n n' : Fin T.t → ℕ) (h : ∀ i, n i ≤ n' i) (x : Fin N) :
    (LL.setTies T n).deg x ≤ (LL.setTies T n').deg x := by
  dsimp only [Letters.setTies]
  split_ifs with hx
  · exact h _
  · exact le_rfl

theorem lattice_theorem_of_discharge (hM : Formalism.GM.M.TheoremM) (hD : HeightBoundImplication) : LatticeTheoremHeightBound := by
  obtain ⟨C₀, hC₀, hM⟩ := hM
  refine ⟨C₀, hC₀, ?_⟩
  intro p _ N r _ _ LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS hdeg hz hκ hineq hL4
  refine hM p N r LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS hdeg hz hκ ?_
  intro n hn
  have hle : ∀ i, n i ≤ n₀ i + dd i * (Yl i - 1) := by
    intro i
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp (Fintype.mem_piFinset.mp hn i)
    rw [← hji]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_sub_one_of_lt (Finset.mem_range.mp hj))) _
  obtain ⟨hP, hW, -⟩ := hD p N r (LL.setTies T n) ρ a κ
    (fun x => (setTies_deg_le LL T n _ hle x).trans (hdeg x)) hineq hκ
  exact ⟨hP, hW, hL4 n hn⟩

end Formalism.InvariantFactorPaths.PW
