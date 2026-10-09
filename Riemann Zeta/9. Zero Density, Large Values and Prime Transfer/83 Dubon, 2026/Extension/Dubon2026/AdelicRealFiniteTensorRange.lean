import Dubon2026.AdelicRealFiniteTensor
import Dubon2026.AdelicRestrictedTensorDensity

/-! # The real and finite tensor spans the entire original adelic cusp space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Original real and finite coordinates run over the whole original adelic unit-reference orbit. -/
theorem adelicRealFiniteMixedFamily_range :
    Set.range (adelicRealFiniteMixedFamily f) = Set.range (fun a : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f a (adelicCyclicUnitReference f)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨rationalAdelicGL2RealFiniteEquiv.symm a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨rationalAdelicGL2RealFiniteEquiv a, ?_⟩
    change adelicCyclicHilbertRepresentation f
      (rationalAdelicGL2RealFiniteEquiv.symm (rationalAdelicGL2RealFiniteEquiv a)) _ = _
    rw [MulEquiv.symm_apply_apply]

/-- The actual real/finite tensor image is exactly the original algebraic unit-reference orbit span. -/
theorem adelicRealFiniteTensorIsometry_range (hf : f ≠ 0) (hk : 0 < k) :
    (adelicRealFiniteTensorIsometry f hf hk).toLinearMap.range =
      Submodule.span ℂ (Set.range (fun a : RationalAdelicGL2 =>
        adelicCyclicHilbertRepresentation f a (adelicCyclicUnitReference f))) := by
  rw [adelicRealFiniteTensorIsometry, gramSpanningIsometry_range, adelicRealFiniteMixedFamily_range]

/-- The genuine real/finite tensor image is dense in the whole original adelic Hilbert space. -/
theorem adelicRealFiniteTensorIsometry_range_closure (hf : f ≠ 0) (hk : 0 < k) :
    (adelicRealFiniteTensorIsometry f hf hk).toLinearMap.range.topologicalClosure = ⊤ := by
  rw [adelicRealFiniteTensorIsometry_range]
  exact adelicCyclicUnitReference_span_closure f hf

end
end Dubon2026
