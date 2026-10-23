import Dubon2026.SourceModularCoefficientResidueDuality
import Dubon2026.SourceCurveRepartitionIndex

/-! DUB-17/18 -> actual modular good reduction -> reverse genus inequality.
The actual coefficient-field residue duality and degree-dimension maximum
give Riemann--Roch and degree(K) = 2 genusFF - 2 in every characteristic.
This uses the existing source H1 genus, with its proved adelic-index bridge.
Exceptional-fiber differential orders and the reverse genus bound remain
separate obligations. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- The actual global index formula, with its parameter identified at the zero divisor. -/
theorem coeff_index_formula (D : Divisor K (modularFunctionFieldCoeff N K)) :
    (ell D : ℤ) - indexOfSpecialty D =
      Divisor.degree D + 1 - indexOfSpecialty (0 : Divisor K (modularFunctionFieldCoeff N K)) := by
  haveI := hasPrincipalDivisors_coeff_field N K
  haveI := finite_coeff_place_residue N K
  haveI := finite_coeff_lSpace N K (0 : Divisor K (modularFunctionFieldCoeff N K))
  obtain ⟨γ, D₀, h⟩ := coeff_degree_dimension_maximum N K
  rw [coeff_index_zero_eq_maximum N K h]
  have hD := (indexOfSpecialty_eq_of_genusReached h D).2
  omega

/-- The canonical divisor space has dimension equal to the actual zero-divisor index. -/
theorem coeff_ell_canonical_eq_zero_index
    {ω : Ω[modularFunctionFieldCoeff N K⁄K]} (hω : ω ≠ 0) :
    ell (coeffCanonicalDivisor N K hω) =
      indexOfSpecialty (0 : Divisor K (modularFunctionFieldCoeff N K)) := by
  simpa only [sub_zero] using (coeff_index_eq_canonical_complement N K hω 0).symm

/-- The actual canonical index is one because global regular functions are the constants. -/
theorem coeff_canonical_index_eq_one
    {ω : Ω[modularFunctionFieldCoeff N K⁄K]} (hω : ω ≠ 0) :
    indexOfSpecialty (coeffCanonicalDivisor N K hω) = 1 := by
  rw [coeff_index_eq_canonical_complement N K hω, sub_self]
  exact finrank_coeff_lSpace_zero N K

/-- The actual canonical divisor has degree twice the zero-divisor index minus two. -/
theorem coeff_canonical_degree_eq_zero_index
    {ω : Ω[modularFunctionFieldCoeff N K⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (coeffCanonicalDivisor N K hω) =
      2 * (indexOfSpecialty (0 : Divisor K (modularFunctionFieldCoeff N K)) : ℤ) - 2 := by
  have h := coeff_index_formula N K (coeffCanonicalDivisor N K hω)
  rw [coeff_ell_canonical_eq_zero_index N K hω, coeff_canonical_index_eq_one N K hω] at h
  omega

/-- Canonical degree is expressed in the source genus defined by the actual H1 quotient. -/
theorem coeff_canonical_degree_eq_genusFF
    {ω : Ω[modularFunctionFieldCoeff N K⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (coeffCanonicalDivisor N K hω) =
      2 * (genusFF K (modularFunctionFieldCoeff N K) : ℤ) - 2 := by
  haveI := hasPrincipalDivisors_coeff_field N K
  rw [genusFF_eq_zero_index]
  exact coeff_canonical_degree_eq_zero_index N K hω

/-- Riemann--Roch for every actual coefficient-field divisor, with the source H1 genus. -/
theorem coeff_functionFieldRiemannRoch
    {ω : Ω[modularFunctionFieldCoeff N K⁄K]} (hω : ω ≠ 0)
    (D : Divisor K (modularFunctionFieldCoeff N K)) :
    (ell D : ℤ) - ell (coeffCanonicalDivisor N K hω - D) =
      Divisor.degree D + 1 - genusFF K (modularFunctionFieldCoeff N K) := by
  haveI := hasPrincipalDivisors_coeff_field N K
  rw [← coeff_index_eq_canonical_complement N K hω D, genusFF_eq_zero_index]
  exact coeff_index_formula N K D

end Dubon2026.SourceFunctionField
