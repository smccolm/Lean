import Dubon2026.AdelicSignedRaisingClosure

/-! # The signed Hilbert basis of the actual full real local factor -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original full real closure carries its literal inherited Hilbert inner product. -/
instance adelicFullRealClosureInner : InnerProductSpace ℂ ((adelicFullRealUnitCore f).topologicalClosure) :=
  @Submodule.innerProductSpace ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance _

/-- Normalizing the actual signed raising family preserves its original algebraic span. -/
theorem adelicNormalizedSignedRaisingJet_span (hf : f ≠ 0) (hk : 0 < k) :
    Submodule.span ℂ (Set.range (adelicNormalizedSignedRaisingJet f)) =
      Submodule.span ℂ (Set.range (adelicSignedRaisingJet f)) :=
  @normalizedOrthogonal_span (AdelicCyclicHilbert f) (ℕ ⊕ ℕ) inferInstance inferInstance
    (adelicSignedRaisingJet f) (adelicSignedRaisingJet_ne_zero f hf hk)

/-- The genuine full real Hilbert factor has the actual signed normalized raising vectors as a Hilbert basis. -/
def adelicFullRealHilbertBasis (hf : f ≠ 0) (hk : 0 < k) :
    HilbertBasis (ℕ ⊕ ℕ) ℂ ((adelicFullRealUnitCore f).topologicalClosure) :=
  orthonormalClosureBasis (adelicNormalizedSignedRaisingJet f)
    (adelicNormalizedSignedRaisingJet_orthonormal f hf hk) ((adelicFullRealUnitCore f).topologicalClosure)
    ((adelicSignedRaisingClosedSpan_eq_fullRealClosure f hf).symm.trans
      (congrArg Submodule.topologicalClosure (adelicNormalizedSignedRaisingJet_span f hf hk)).symm)

/-- The full real Hilbert basis is literally the normalized original raising and reflected raising family. -/
theorem adelicFullRealHilbertBasis_apply (hf : f ≠ 0) (hk : 0 < k) (i : ℕ ⊕ ℕ) :
    (adelicFullRealHilbertBasis f hf hk i).val = adelicNormalizedSignedRaisingJet f i :=
  orthonormalClosureBasis_apply (adelicNormalizedSignedRaisingJet f)
    (adelicNormalizedSignedRaisingJet_orthonormal f hf hk) ((adelicFullRealUnitCore f).topologicalClosure) _ i

end
end Dubon2026
