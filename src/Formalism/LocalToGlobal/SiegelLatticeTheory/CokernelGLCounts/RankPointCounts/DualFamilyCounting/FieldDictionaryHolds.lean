import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem field_dictionary_holds : HostDict := by
  intro D
  exact ⟨D.sp.cm.cmUnram, fun a => by rw [D.sp.cm.fixed a, RingHom.mem_range, Set.mem_range],
    fun x hx => (D.sp.Y 0).nondeg.1 x hx⟩

end Formalism.L2.SG.Pf.Cnt
