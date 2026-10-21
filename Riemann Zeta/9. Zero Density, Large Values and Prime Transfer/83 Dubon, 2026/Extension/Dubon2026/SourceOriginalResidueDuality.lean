import Dubon2026.SourceOriginalGlobalResidues
import Dubon2026.SourceOriginalWeilRank

/-! DUB-17/18 -> original regular differential dimension -> Riemann--Roch.
The actual nonzero residue functional now annihilates global functions and
has exactly the canonical divisor as its maximal bound. The existing proved
Weil rank-one theorem makes its residue pairing bijective, identifying the
actual index of specialty with the complementary canonical divisor space.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem originalResidueFunctional_mem_omegaSpace
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0) :
    originalResidueFunctional N L hω ∈ omegaSpace (originalCanonicalDivisor N L hω) := by
  rw [omegaSpace, Submodule.mem_dualAnnihilator]
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Submodule.mem_sup.mp hα
  rw [map_add, originalResidueFunctional_vanish_canonical N L hω
    (Submodule.mem_comap.mp hβ), zero_add]
  obtain ⟨f, hf⟩ := Submodule.mem_comap.mp hγ
  have he : originalPrincipalAdele N L f = γ := Subtype.ext hf
  rw [← he]
  exact originalResidueFunctional_diagonal_zero N L hω f

theorem originalResidueFunctional_omegaSpace_max
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0)
    (D : Divisor L (modularFunctionFieldOver N L))
    (hD : originalResidueFunctional N L hω ∈ omegaSpace D) :
    D ≤ originalCanonicalDivisor N L hω :=
  (originalResidueFunctional_vanish_bound_iff N L hω D).mp
    (fun _ hα => omegaSpace_vanishBdd hD hα)

theorem original_residue_pairing_bijective
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0)
    (D : Divisor L (modularFunctionFieldOver N L)) :
    letI := hasPrincipalDivisors_original N L
    Function.Bijective (residuePairing L (modularFunctionFieldOver N L)
      (originalCanonicalDivisor N L hω) D (originalResidueFunctional_mem_omegaSpace N L hω)) := by
  letI := hasPrincipalDivisors_original N L
  exact ⟨residuePairing_injective _ D (originalResidueFunctional_mem_omegaSpace N L hω)
      (originalResidueFunctional_ne_zero N L hω),
    residuePairing_surjective_of_rankOne_max (original_weil_differentials_rank_one N L)
      (originalResidueFunctional_mem_omegaSpace N L hω)
      (originalResidueFunctional_ne_zero N L hω)
      (originalResidueFunctional_omegaSpace_max N L hω) D⟩

/-- The actual original residue pairing identifies complementary divisor spaces and dual indices. -/
def originalResiduePairingEquiv
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0)
    (D : Divisor L (modularFunctionFieldOver N L)) :
    LSpace (originalCanonicalDivisor N L hω - D) ≃ₗ[L] omegaSpace D := by
  letI := hasPrincipalDivisors_original N L
  exact LinearEquiv.ofBijective _ (original_residue_pairing_bijective N L hω D)

theorem original_index_eq_canonical_complement
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0)
    (D : Divisor L (modularFunctionFieldOver N L)) :
    indexOfSpecialty D = ell (originalCanonicalDivisor N L hω - D) := by
  rw [← finrank_omegaSpace_eq_indexOfSpecialty]
  exact (originalResiduePairingEquiv N L hω D).finrank_eq.symm

end
end Dubon2026.SourceFunctionField
