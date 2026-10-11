import Dubon2026.MatrixAdicHopfFlatCondition
import Dubon2026.FiniteFlatSchemeModelEquivalence

/-! # The original geometric finite-flat condition at every positive adic level

The scheme-side condition retains every original quotient representation and its
specified Galois action. Its equivalence with the coordinate condition uses both
directions of the genuine scheme/Hopf-model reconstruction.
-/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable (R F K : Type u) {ι A : Type u}
  [CommRing R] [Field F] [Field K] [Algebra R F] [Algebra F K] [Algebra R K]
  [IsScalarTower R F K] [Fintype ι] [DecidableEq ι] [CommRing A] [IsLocalRing A]

/-- Every positive original maximal-adic quotient representation is realized by
an actual finite flat commutative group scheme over the original integral base.
This is a definition of the geometric condition, not an arithmetic existence theorem. -/
def MatrixAdicFiniteFlatScheme (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) : Prop :=
  ∀ n : ℕ, 0 < n →
    FiniteFlatSchemePointRealization (R := R) (F := F) (K := K)
      (matrixUnderlyingGroupAction
        (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal A ^ n) ρ))

variable {R F K} [IsDomain R] [IsPrincipalIdealRing R]

/-- The actual all-level coordinate-model condition is exactly the actual geometric
finite-flat condition. Each direction constructs the corresponding original model
at every positive level, without changing the quotient matrices or Galois action. -/
theorem matrixAdicHopfFlat_iff_finiteFlatScheme
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) :
    MatrixAdicHopfFlat R F K ρ ↔ MatrixAdicFiniteFlatScheme R F K ρ := by
  constructor
  · intro h n hn
    exact (finiteFreeHopfPointModel_iff_schemeRealization _).mp (h n hn)
  · intro h n hn
    exact (finiteFreeHopfPointModel_iff_schemeRealization _).mpr (h n hn)

/-- The original geometric condition is invariant under the same actual change of
basis, by the proved original-coordinate equivalence and conjugacy transport. -/
theorem matrixAdicFiniteFlatScheme_conjugacy_iff
    (ρ τ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A) (U : GeneralLinearGroup ι A)
    (hc : ∀ g, τ g = U * ρ g * U⁻¹) :
    MatrixAdicFiniteFlatScheme R F K ρ ↔ MatrixAdicFiniteFlatScheme R F K τ := by
  exact (matrixAdicHopfFlat_iff_finiteFlatScheme ρ).symm.trans
    ((matrixAdicHopfFlat_conjugacy_iff ρ τ U hc).trans
      (matrixAdicHopfFlat_iff_finiteFlatScheme τ))

end
end Dubon2026
