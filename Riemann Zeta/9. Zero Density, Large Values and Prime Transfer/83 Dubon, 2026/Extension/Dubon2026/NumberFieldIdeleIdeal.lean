import Dubon2026.NumberFieldIdeleOrders

/-! # The actual fractional ideal of an original idele

The finite product of original prime ideals with the proved original
idele orders has exactly those multiplicities. On principal ideles it
is the existing actual principal ideal. This suffices for the finite
ideal-class representative argument that makes supported ideles onto
the global classes, a necessary step in DUB-17's global norm-index route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors
variable (K : Type) [Field K] [NumberField K]

/-- The invertible fractional ideal obtained from the original finite idele orders. -/
def numberFieldIdeleIdeal (a : (AdeleRing (𝓞 K) K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (∏ᶠ v : HeightOneSpectrum (𝓞 K),
    (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ numberFieldIdeleOrder K a v) (by
      apply finprod_ne_zero
      intro v
      exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))

/-- Every prime multiplicity of the actual associated ideal is the original idele order. -/
theorem numberFieldIdeleIdeal_count (a : (AdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (numberFieldIdeleIdeal K a).val = numberFieldIdeleOrder K a v := by
  apply FractionalIdeal.count_finprod
  exact Filter.eventually_cofinite.mpr (numberFieldIdeleOrder_finite_support K a)

/-- The ideal of an original principal idele is its original principal fractional ideal. -/
theorem numberFieldIdeleIdeal_principal (x : Kˣ) :
    numberFieldIdeleIdeal K (numberFieldPrincipalIdele K x) = toPrincipalIdeal (𝓞 K) K x := by
  apply Units.ext
  apply fractionalIdeal_eq_of_counts (Units.ne_zero _) (Units.ne_zero _)
  intro v
  rw [numberFieldIdeleIdeal_count, numberFieldIdeleOrder_principal]

end
end Dubon2026
