import Dubon2026.SourceModularCoefficientGlobalFunctional
import Dubon2026.SourceModularCoefficientWeilRank

/-! DUB-17/18 -> good reduction -> reverse genus inequality -> canonical
 degree. Reuse the existing proved Weil rank-one and residue-pairing
 machinery on the actual modular coefficient field. Global vanishing,
 nonzero residue functionals and the maximal canonical bound are all
 derived, in every characteristic. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [IsAlgClosed L]

theorem coeffResidueFunctional_mem_omegaSpace
    {ω : Ω[modularFunctionFieldCoeff N L⁄L]} (hω : ω ≠ 0) :
    coeffResidueFunctional N L hω ∈ omegaSpace (coeffCanonicalDivisor N L hω) := by
  rw [omegaSpace, Submodule.mem_dualAnnihilator]
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Submodule.mem_sup.mp hα
  rw [map_add, coeffResidueFunctional_vanish_canonical N L hω
    (Submodule.mem_comap.mp hβ), zero_add]
  obtain ⟨f, hf⟩ := Submodule.mem_comap.mp hγ
  have he : coeffPrincipalAdele N L f = γ := Subtype.ext hf
  rw [← he]
  exact coeffResidueFunctional_diagonal_zero N L hω f

theorem coeffResidueFunctional_omegaSpace_max
    {ω : Ω[modularFunctionFieldCoeff N L⁄L]} (hω : ω ≠ 0)
    (D : Divisor L (modularFunctionFieldCoeff N L))
    (hD : coeffResidueFunctional N L hω ∈ omegaSpace D) :
    D ≤ coeffCanonicalDivisor N L hω :=
  (coeffResidueFunctional_vanish_bound_iff N L hω D).mp
    (fun _ hα => omegaSpace_vanishBdd hD hα)

theorem coeff_residue_pairing_bijective
    {ω : Ω[modularFunctionFieldCoeff N L⁄L]} (hω : ω ≠ 0)
    (D : Divisor L (modularFunctionFieldCoeff N L)) :
    letI := hasPrincipalDivisors_coeff_field N L
    Function.Bijective (residuePairing L (modularFunctionFieldCoeff N L)
      (coeffCanonicalDivisor N L hω) D (coeffResidueFunctional_mem_omegaSpace N L hω)) := by
  letI := hasPrincipalDivisors_coeff_field N L
  exact ⟨residuePairing_injective _ D (coeffResidueFunctional_mem_omegaSpace N L hω)
      (coeffResidueFunctional_ne_zero N L hω),
    residuePairing_surjective_of_rankOne_max (coeff_weil_differentials_rank_one N L)
      (coeffResidueFunctional_mem_omegaSpace N L hω)
      (coeffResidueFunctional_ne_zero N L hω)
      (coeffResidueFunctional_omegaSpace_max N L hω) D⟩

/-- The actual coefficient-field residue pairing identifies complementary divisor spaces and dual indices. -/
def coeffResiduePairingEquiv
    {ω : Ω[modularFunctionFieldCoeff N L⁄L]} (hω : ω ≠ 0)
    (D : Divisor L (modularFunctionFieldCoeff N L)) :
    LSpace (coeffCanonicalDivisor N L hω - D) ≃ₗ[L] omegaSpace D := by
  letI := hasPrincipalDivisors_coeff_field N L
  exact LinearEquiv.ofBijective _ (coeff_residue_pairing_bijective N L hω D)

theorem coeff_index_eq_canonical_complement
    {ω : Ω[modularFunctionFieldCoeff N L⁄L]} (hω : ω ≠ 0)
    (D : Divisor L (modularFunctionFieldCoeff N L)) :
    indexOfSpecialty D = ell (coeffCanonicalDivisor N L hω - D) := by
  rw [← finrank_omegaSpace_eq_indexOfSpecialty]
  exact (coeffResiduePairingEquiv N L hω D).finrank_eq.symm

end
end Dubon2026.SourceFunctionField
