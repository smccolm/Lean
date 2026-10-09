import Dubon2026.AdelicBadRealTensorBase
import Dubon2026.AdelicFiniteRealTensorAction
import Dubon2026.AdelicRestrictedFiniteTensorAction

/-! # The genuine fixed-base tensor factorization is equivariant for all original bad and real coordinates -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- The actual isometric factorization of the original fixed base intertwines the independently constructed finite bad/real tensor action on every original vector. -/
theorem adelicBadRealTensorBaseEquiv_intertwines (hk : 0 < k)
    (a : AdelicBadLocalTuple N × GeneralLinearGroup (Fin 2) ℝ)
    (x : AdelicFiniteRealTensor F.toCuspForm (adelicBadPlaceFamily N)) :
    adelicBadRealTensorBaseEquiv F hk
      (adelicFiniteRealTensorRepresentation F.toCuspForm (adelicBadPlaceFamily N) a x) =
      adelicRestrictedBaseCoreRepresentation F.toCuspForm (adelicBadRealBaseEquiv N a)
        (adelicBadRealTensorBaseEquiv F hk x) := by
  apply Subtype.ext
  exact adelicFiniteRealTensorIsometry_intertwines (adelicBadPlaceFamily N) F
    (adelicBadPlaceFamily_injective N) hk a x

end
end Dubon2026
