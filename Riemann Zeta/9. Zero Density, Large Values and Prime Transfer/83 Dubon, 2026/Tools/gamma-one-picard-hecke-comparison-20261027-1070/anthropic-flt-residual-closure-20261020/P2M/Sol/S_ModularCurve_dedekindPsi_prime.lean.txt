import Definitions.Def_ModularCurve_X0
import P2M.Util
namespace P2MW.S_ModularCurve_dedekindPsi_prime

open ModularCurve IntermediateField

noncomputable section

theorem solution {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 :=by
  rw [dedekindPsi, Finset.sum_filter, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  simp [hp.squarefree, Nat.div_self hp.pos]

end
