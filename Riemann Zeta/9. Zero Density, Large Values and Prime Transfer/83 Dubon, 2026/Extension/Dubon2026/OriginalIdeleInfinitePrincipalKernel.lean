import Dubon2026.OriginalIdeleInfiniteH2
import Dubon2026.OriginalCyclicClassH2Surjectivity

/-! # The actual class kernel on the zero-infinite part

Original sequence exactness supplies the principal preimage, and the
literal localization square derives its infinite vanishing. This removes
the class-kernel premise in DUB-17's auxiliary normalization comparison.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- Principal reciprocity on the original zero-infinite part kills the
actual class-map kernel on that same part; its principal preimage is derived. -/
theorem originalFullIdele_total_zero_of_class_zero_of_infinite
    (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (hkill : ∀ y : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2,
      (∀ v : NumberField.InfinitePlace L, originalGlobalInfiniteH2 K L v y = 0) →
      total ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) y) = 0)
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hInf : ∀ v : NumberField.InfinitePlace L, originalFullIdeleInfiniteH2 K L v x = 0)
    (hx : (groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x = 0) :
    total x = 0 := by
  have hk : x ∈ LinearMap.ker
      ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L)).hom := hx
  rw [originalFullClassH2_ker_eq_principal_range K L] at hk
  obtain ⟨y, hy⟩ := hk
  have hyInf (v : NumberField.InfinitePlace L) : originalGlobalInfiniteH2 K L v y = 0 := by
    rw [← originalFullIdeleInfiniteH2_principal K L v y]
    exact (congrArg (originalFullIdeleInfiniteH2 K L v) hy).trans (hInf v)
  exact (congrArg total hy).symm.trans (hkill y hyInf)

end
end Dubon2026
