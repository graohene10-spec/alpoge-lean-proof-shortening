import Formalism.RealPlaceAnalysis.StatementA
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CasimirCommutation

open scoped TensorProduct
open Finset

noncomputable section

namespace Formalism.REAL

theorem casComm_casK_comm {A : Type} [Ring A] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → A) (hE : GlRel E) (c d : Fin n) (hcd : ε c = ε d) :
    CasK ε E * E c d = E c d * CasK ε E :=
  _root_.UpperTheory.Reformulated.B.CasimirCommutation.casComm_casK_comm ε E hE c d hcd

theorem casimir_central_holds : CasCentral := by
  intro A _ n ε E hE
  refine ⟨fun c d => ?_, fun c d h => casComm_casK_comm ε E hE c d h⟩
  simpa [CasK, Cas] using casComm_casK_comm (fun _ => true) E hE c d rfl

end Formalism.REAL
