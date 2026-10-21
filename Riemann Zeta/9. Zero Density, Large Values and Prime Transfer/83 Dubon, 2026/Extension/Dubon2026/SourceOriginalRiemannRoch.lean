import Dubon2026.SourceOriginalResidueDuality
import Dubon2026.SourceOriginalCanonicalDegree

/-! DUB-17/18 -> original parabolic realization -> matching cusp-form
dimension -> regular differential dimension. The proved original global
index and residue duality give Riemann--Roch for every actual divisor. They
identify the zero index, canonical degree genus and regular differential
dimension. The numerical modular genus and analytic realization remain
separate obligations; neither is assumed here.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem original_ell_zero : ell (0 : Divisor L (modularFunctionFieldOver N L)) = 1 := by
  rw [ell, original_lSpace_zero_eq_range N L, LinearMap.finrank_range_of_inj
    (f := Algebra.linearMap L (modularFunctionFieldOver N L))
    (algebraMap L (modularFunctionFieldOver N L)).injective, Module.finrank_self]

theorem original_ell_canonical_eq_zero_index
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0) :
    ell (originalCanonicalDivisor N L hω) =
      indexOfSpecialty (0 : Divisor L (modularFunctionFieldOver N L)) := by
  simpa only [sub_zero] using (original_index_eq_canonical_complement N L hω 0).symm

theorem original_canonical_index_eq_one
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0) :
    indexOfSpecialty (originalCanonicalDivisor N L hω) = 1 := by
  rw [original_index_eq_canonical_complement N L hω, sub_self, original_ell_zero N L]

theorem original_canonical_degree_eq_zero_index
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0) :
    Divisor.degree (originalCanonicalDivisor N L hω) =
      2 * (indexOfSpecialty (0 : Divisor L (modularFunctionFieldOver N L)) : ℤ) - 2 := by
  have h := original_index_formula N L (originalCanonicalDivisor N L hω)
  rw [original_ell_canonical_eq_zero_index N L hω,
    original_canonical_index_eq_one N L hω] at h
  omega

theorem originalGenus_eq_zero_index :
    originalGenus N L = indexOfSpecialty (0 : Divisor L (modularFunctionFieldOver N L)) := by
  rw [originalGenus_eq_jCanonical_degree]
  have hd := original_canonical_degree_eq_zero_index N L (D_jOver_ne_zero N L)
  omega

theorem original_functionFieldRiemannRoch
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0)
    (D : Divisor L (modularFunctionFieldOver N L)) :
    (ell D : ℤ) - ell (originalCanonicalDivisor N L hω - D) =
      Divisor.degree D + 1 - originalGenus N L := by
  rw [← original_index_eq_canonical_complement N L hω D, originalGenus_eq_zero_index]
  exact original_index_formula N L D

theorem finrank_original_regularDifferentials_eq_genus :
    Module.finrank L (regularDifferentials L (modularFunctionFieldOver N L)) =
      originalGenus N L := by
  rw [finrank_original_regularDifferentials_eq_canonicalSpace]
  change ell (originalCanonicalDivisor N L (D_jOver_ne_zero N L)) = originalGenus N L
  rw [original_ell_canonical_eq_zero_index, originalGenus_eq_zero_index]

end
end Dubon2026.SourceFunctionField
