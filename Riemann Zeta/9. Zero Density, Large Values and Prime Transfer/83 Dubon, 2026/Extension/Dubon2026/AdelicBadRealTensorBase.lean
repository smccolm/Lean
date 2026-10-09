import Dubon2026.AdelicFiniteRealTensor
import Dubon2026.AdelicBadRealBaseCoordinates

/-! # The genuine finite bad-place and real tensor is exactly the original fixed base core -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Genuine bad/real coordinates run through exactly the original fixed-base unit-reference orbit. -/
theorem adelicBadRealMixedFamily_range :
    Set.range (adelicFiniteRealMixedFamily f (adelicBadPlaceFamily N) (adelicBadPlaceFamily_injective N)) =
      Set.range (fun b : adelicRestrictedBaseGroup N => adelicRestrictedBaseRepresentation f b (adelicCyclicUnitReference f)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨adelicBadRealBaseEquiv N a, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := (adelicBadRealBaseEquiv N).surjective b
    exact ⟨a, rfl⟩

variable (F : PrimitiveCuspForm N k)

/-- The original bad/real tensor map has exactly the genuine fixed-base algebraic orbit core as its range. -/
theorem adelicBadRealTensorIsometry_range (hk : 0 < k) :
    (adelicFiniteRealTensorIsometry (adelicBadPlaceFamily N) F (adelicBadPlaceFamily_injective N) hk).toLinearMap.range =
      adelicRestrictedBaseCore F.toCuspForm := by
  rw [adelicFiniteRealTensorIsometry, gramSpanningIsometry_range]
  exact congrArg (Submodule.span ℂ) (adelicBadRealMixedFamily_range F.toCuspForm)

/-- The independently normed tensor of all original bad local cores and the full real core is genuinely isometrically equivalent to the original fixed base core. -/
def adelicBadRealTensorBaseEquiv (hk : 0 < k) :
    AdelicFiniteRealTensor F.toCuspForm (adelicBadPlaceFamily N) ≃ₗᵢ[ℂ] adelicRestrictedBaseCore F.toCuspForm :=
  (adelicFiniteRealTensorIsometry (adelicBadPlaceFamily N) F (adelicBadPlaceFamily_injective N) hk).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (adelicBadRealTensorIsometry_range F hk))

/-- The genuine fixed-base equivalence retains exactly the original bad/real tensor vector in the ambient adelic Hilbert space. -/
theorem adelicBadRealTensorBaseEquiv_val (hk : 0 < k)
    (x : AdelicFiniteRealTensor F.toCuspForm (adelicBadPlaceFamily N)) :
    (adelicBadRealTensorBaseEquiv F hk x).val =
      adelicFiniteRealTensorIsometry (adelicBadPlaceFamily N) F (adelicBadPlaceFamily_injective N) hk x := rfl

/-- The genuine bad/real factor equivalence sends each original pure orbit tensor to its literal original fixed-base orbit vector. -/
theorem adelicBadRealTensorBaseEquiv_family (hk : 0 < k)
    (a : AdelicBadLocalTuple N × GeneralLinearGroup (Fin 2) ℝ) :
    adelicBadRealTensorBaseEquiv F hk (adelicFiniteRealTensorFamily F.toCuspForm (adelicBadPlaceFamily N) a) =
      adelicRestrictedBaseOrbit F.toCuspForm (adelicBadRealBaseEquiv N a) := by
  apply Subtype.ext
  exact adelicFiniteRealTensorIsometry_family (adelicBadPlaceFamily N) F (adelicBadPlaceFamily_injective N) hk a

end
end Dubon2026
