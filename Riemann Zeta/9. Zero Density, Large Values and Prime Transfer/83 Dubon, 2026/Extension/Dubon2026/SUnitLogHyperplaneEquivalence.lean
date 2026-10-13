import Dubon2026.SUnitLogHyperplaneReduction
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Exact full and reduced S-unit logarithmic coordinates

The actual coordinate-sum form is nonzero. Rank-nullity and the existing
Dirichlet dimension make the already injective original reduction an
equivalence. This avoids a separate inverse construction while retaining
the exact original logarithms needed by DUB-17's S-unit Herbrand input.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The original all-place coordinate sum is nonzero at an original infinite coordinate. -/
theorem sUnitLogCoordinateSum_ne_zero : sUnitLogCoordinateSum K S ≠ 0 := by
  intro h
  have he := congrArg (fun f : SUnitFullLogSpace K S →ₗ[ℝ] ℝ =>
    f (Pi.single (Sum.inl (Units.dirichletUnitTheorem.w₀ (K := K))) 1)) h
  change (∑ p : SUnitLogPlace K S,
    Pi.single (Sum.inl (Units.dirichletUnitTheorem.w₀ (K := K))) (1 : ℝ) p) = 0 at he
  have hs : (∑ p : SUnitLogPlace K S,
      Pi.single (Sum.inl (Units.dirichletUnitTheorem.w₀ (K := K))) (1 : ℝ) p) = 1 := by
    rw [Fintype.sum_eq_single (Sum.inl (Units.dirichletUnitTheorem.w₀ (K := K)))]
    · simp
    · intro p hp
      exact Pi.single_eq_of_ne hp _
  rw [hs] at he
  exact one_ne_zero he

/-- The original sum-zero hyperplane has the same dimension as the original reduced space. -/
theorem sUnitLogHyperplane_finrank :
    Module.finrank ℝ (SUnitLogHyperplane K S) = Units.rank K + S.card := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero (sUnitLogCoordinateSum_ne_zero K S)
  have hp : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
  have hd : Module.finrank ℝ (SUnitFullLogSpace K S) =
      Fintype.card (InfinitePlace K) + S.card := by
    simp [SUnitFullLogSpace, SUnitLogPlace]
  rw [hd] at h
  change Module.finrank ℝ (SUnitLogHyperplane K S) + 1 = _ at h
  unfold Units.rank
  omega

/-- The original full-to-reduced logarithmic map is a linear equivalence. -/
def sUnitLogHyperplaneEquiv : SUnitLogHyperplane K S ≃ₗ[ℝ] SUnitReducedLogSpace K S :=
  (sUnitLogHyperplaneReduction K S).linearEquivOfInjective
    (sUnitLogHyperplaneReduction_injective K S)
    (by rw [sUnitLogHyperplane_finrank, sUnitReducedLogSpace_finrank])

/-- The exact coordinate equivalence sends the original full logarithm to the original reduced one. -/
theorem sUnitLogHyperplaneEquiv_fullLog
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    sUnitLogHyperplaneEquiv K S (sUnitFullLog K S x) = sUnitReducedLog K S x :=
  sUnitLogHyperplaneReduction_fullLog K S x

end
end Dubon2026
