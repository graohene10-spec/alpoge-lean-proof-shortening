import Formalism.LocalToGlobal.ClassS

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

theorem gTiedF_of_C2S {eps : ℝ} (Fm : FamP eps) (h : LinkedFamiliesLevelClass Fm) : G.GroupCompatibilityFamily Fm := by
  obtain ⟨x0, hx0⟩ := h
  exact ⟨max x0 (Fm.x1 + 1), fun x hx i hx1 =>
    (hx0 x hx1 ((le_max_left _ _).trans hx) i).elim fun T => ⟨T.g⟩⟩

end Formalism.L2
