import Dubon2026.SourceInducedCoefficientDifferential
import Dubon2026.SourceCoefficientHighest
import Dubon2026.SourceInducedLieIrreducible
import Dubon2026.SourceRegularSpecialLinearStability

/-! Lie stability of the actual integral generic-fibre image.
Original integral differentials preserve the original integral covariance.
Their coefficient-change compatibility therefore makes the field span
stable under the actual field special-linear action.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable (n : ℕ) (lam : Fin n → ℤ)

/-- The field span of the actual integral coefficient image is stable under every original off-diagonal differential. -/
theorem sourceCoefficientSpan_offDiagonal (i j : Fin n)
    (p : generalLinearIntegralInducedSubmodule K n lam)
    (hp : p ∈ Submodule.span K (LinearMap.range (sourceInducedCoefficientMap R K n lam))) :
    sourceInducedDifferential K n lam (Matrix.single i j 1) p ∈
      Submodule.span K (LinearMap.range (sourceInducedCoefficientMap R K n lam)) := by
  let F := sourceInducedCoefficientMap R K n lam
  let W : Submodule K (generalLinearIntegralInducedSubmodule K n lam) :=
    Submodule.span K (LinearMap.range F)
  let D := sourceInducedDifferential K n lam (Matrix.single i j 1)
  have hs : W ≤ W.comap D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    have he : D (F q) = F (sourceInducedDifferential R n lam (Matrix.single i j 1) q) := by
      have hm : (Matrix.single i j (1 : R)).map (algebraMap R K) =
          Matrix.single i j (1 : K) := by
        ext a b
        by_cases ha : i = a <;> by_cases hb : j = b <;>
          simp [ha, hb]
      have hd := sourceInducedCoefficientMap_differential R K n lam
        (Matrix.single i j 1) q
      rw [hm] at hd
      exact hd.symm
    change D (F q) ∈ W
    rw [he]
    exact Submodule.subset_span (LinearMap.mem_range_self _ _)
  exact hs hp

/-- The actual field span of the original integral coefficient image is an invariant subspace of the actual source special-linear Lie action. -/
theorem sourceCoefficientSpan_lie_mem
    (X : LieAlgebra.SpecialLinear.sl (Fin n) K)
    (p : generalLinearIntegralInducedSubmodule K n lam)
    (hp : p ∈ Submodule.span K (LinearMap.range (sourceInducedCoefficientMap R K n lam))) :
    ⁅X, p⁆ ∈ Submodule.span K (LinearMap.range (sourceInducedCoefficientMap R K n lam)) := by
  let W : Submodule K (generalLinearIntegralInducedSubmodule K n lam) :=
    Submodule.span K (LinearMap.range (sourceInducedCoefficientMap R K n lam))
  let V := W.map (generalLinearIntegralInducedSubmodule K n lam).subtype
  have hoff (i j : Fin n) (_ : i ≠ j) (q : GeneralLinearRegularFunctions K n)
      (hq : q ∈ V) : sourceRegularDifferential (Matrix.single i j (1 : K)) q ∈ V := by
    obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.mp hq
    exact Submodule.mem_map.mpr
      ⟨sourceInducedDifferential K n lam (Matrix.single i j 1) r,
        sourceCoefficientSpan_offDiagonal R K n lam i j r hr, rfl⟩
  have hm : p.val ∈ V := Submodule.mem_map.mpr ⟨p, hp, rfl⟩
  have hd := sourceRegular_traceZero_stable_of_offDiagonal V hoff X.val X.property p.val hm
  obtain ⟨q, hq, he⟩ := Submodule.mem_map.mp hd
  have hqeq : q = ⁅X, p⁆ := Subtype.ext he
  rwa [hqeq] at hq

/-- The actual integral coefficient image, spanned over the field and equipped with its derived original Lie invariance. -/
def sourceCoefficientSpanLieSubmodule :
    LieSubmodule K (LieAlgebra.SpecialLinear.sl (Fin n) K)
      (generalLinearIntegralInducedSubmodule K n lam) where
  toSubmodule := Submodule.span K (LinearMap.range (sourceInducedCoefficientMap R K n lam))
  lie_mem := fun {X p} hp => sourceCoefficientSpan_lie_mem R K n lam X p hp

end
end Dubon2026
