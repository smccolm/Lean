import Dubon2026.SUnitLogarithmicExactSequence

/-! # Splitting off the invariant logarithmic diagonal

The original all-place coordinate space splits into its actual sum-zero
hyperplane and the invariant diagonal. This is the required one-dimensional
correction between the S-unit lattice and the permutation representation
in DUB-17's Herbrand-quotient calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))

/-- The constant original all-place vector whose coordinate sum is one. -/
def sUnitLogDiagonal : SUnitFullLogSpace L S :=
  fun _ => (Fintype.card (SUnitLogPlace L S) : ℝ)⁻¹

/-- The original normalized diagonal has coordinate sum one. -/
theorem sUnitLogCoordinateSum_diagonal :
    sUnitLogCoordinateSum L S (sUnitLogDiagonal L S) = 1 := by
  change (∑ _ : SUnitLogPlace L S, (Fintype.card (SUnitLogPlace L S) : ℝ)⁻¹) = 1
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

/-- The exact original coordinate-sum splitting with its original sum-zero first component. -/
def sUnitLogDiagonalSplit : SUnitFullLogSpace L S →ₗ[ℝ] SUnitLogHyperplane L S × ℝ where
  toFun z := (⟨z - sUnitLogCoordinateSum L S z • sUnitLogDiagonal L S, by
    change sUnitLogCoordinateSum L S _ = 0
    rw [map_sub, map_smul, sUnitLogCoordinateSum_diagonal]
    simp⟩, sUnitLogCoordinateSum L S z)
  map_add' z y := by
    apply Prod.ext
    · apply Subtype.ext
      change z + y - sUnitLogCoordinateSum L S (z + y) • sUnitLogDiagonal L S =
        (z - sUnitLogCoordinateSum L S z • sUnitLogDiagonal L S) +
          (y - sUnitLogCoordinateSum L S y • sUnitLogDiagonal L S)
      rw [map_add, add_smul]
      abel
    · exact map_add _ z y
  map_smul' c z := by
    apply Prod.ext
    · apply Subtype.ext
      change c • z - sUnitLogCoordinateSum L S (c • z) • sUnitLogDiagonal L S =
        c • (z - sUnitLogCoordinateSum L S z • sUnitLogDiagonal L S)
      rw [map_smul, smul_sub, smul_smul]
      rfl
    · exact map_smul _ c z

/-- Both original split components determine the original full coordinate vector. -/
theorem sUnitLogDiagonalSplit_injective : Function.Injective (sUnitLogDiagonalSplit L S) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  have hs : sUnitLogCoordinateSum L S z = 0 := congrArg Prod.snd hz
  have hh := congrArg (fun p : SUnitLogHyperplane L S × ℝ => p.1.val) hz
  change z - sUnitLogCoordinateSum L S z • sUnitLogDiagonal L S = 0 at hh
  simpa only [hs, zero_smul, sub_zero] using hh

/-- Every original hyperplane vector and diagonal coordinate has an original full-vector preimage. -/
theorem sUnitLogDiagonalSplit_surjective : Function.Surjective (sUnitLogDiagonalSplit L S) := by
  rintro ⟨z, t⟩
  refine ⟨z.val + t • sUnitLogDiagonal L S, ?_⟩
  have hs : sUnitLogCoordinateSum L S (z.val + t • sUnitLogDiagonal L S) = t := by
    rw [map_add, map_smul, sUnitLogCoordinateSum_diagonal, z.property]
    simp
  apply Prod.ext
  · apply Subtype.ext
    change z.val + t • sUnitLogDiagonal L S -
      sUnitLogCoordinateSum L S (z.val + t • sUnitLogDiagonal L S) • sUnitLogDiagonal L S = z.val
    rw [hs, add_sub_cancel_right]
  · exact hs

/-- The original full logarithmic space is the actual hyperplane plus its invariant diagonal. -/
def sUnitLogDiagonalEquiv : SUnitFullLogSpace L S ≃ₗ[ℝ] SUnitLogHyperplane L S × ℝ :=
  LinearEquiv.ofBijective (sUnitLogDiagonalSplit L S)
    ⟨sUnitLogDiagonalSplit_injective L S, sUnitLogDiagonalSplit_surjective L S⟩

end
end Dubon2026
