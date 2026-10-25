import Dubon2026.SourceOriginalWeilCoverCanonicalSupport
import Dubon2026.SourceCurveFiniteCoordinateResidueDuality

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> prescribed residues.
The native finite-coordinate index and residue-duality theorems give exactly
the Riemann--Roch identity needed for two-pole dimension growth. Only existence
of its common integer constant is used; no numerical genus formula is needed. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)

/-- The actual order divisor of a nonzero differential on the cover field. -/
def coverCanonicalDivisor {ω : Ω[EE⁄ℂ]} (hω : ω ≠ 0) : Divisor ℂ EE :=
  Finsupp.ofSupportFinite (fun v => v.ordDifferential ω)
    (finite_cover_differential_support N n r hω)

theorem coverCanonicalDivisor_apply {ω : Ω[EE⁄ℂ]} (hω : ω ≠ 0) (v : Place ℂ EE) :
    coverCanonicalDivisor N n r hω v = v.ordDifferential ω := rfl

theorem exists_cover_riemann_roch_constant :
    ∃ γ : ℤ, ∀ {ω : Ω[EE⁄ℂ]} (hω : ω ≠ 0) (D : Divisor ℂ EE),
      (ell D : ℤ) - ell (coverCanonicalDivisor N n r hω - D) =
        Divisor.degree D + 1 - γ := by
  letI := (originalWeilKummerCover_finite_coordinate N ℂ n r).2
  letI := originalWeilKummerCover_curve N ℂ n r
  letI : ∀ v : Place ℂ EE, Module.Finite ℂ v.ResidueField :=
    (originalWeilKummerCover_curve N ℂ n r).finiteResidue
  let Q : Place ℂ EE := Classical.choice (nonempty_cover_place N n r)
  letI := finite_cover_lSpace N n r Q (0 : Divisor ℂ EE)
  obtain ⟨γ, D₀, hmax⟩ := finite_coordinate_degree_dimension_maximum
    (algebraMap FF EE (jOver N ℂ)) (originalWeilKummerCover_finite_coordinate N ℂ n r).1
  refine ⟨γ, fun {ω} hω D => ?_⟩
  letI := hasCanonicalDivisor_finite_coordinate (algebraMap FF EE (jOver N ℂ))
    (originalWeilKummerCover_finite_coordinate N ℂ n r).1
    (cover_coordinate_differential_ne_zero N n r)
  have heq : canonicalDivisorOf hω = coverCanonicalDivisor N n r hω := by
    ext v
    rw [canonicalDivisorOf_apply, coverCanonicalDivisor_apply]
  have hidx := finite_coordinate_index_eq_canonical_complement
    (algebraMap FF EE (jOver N ℂ)) (originalWeilKummerCover_finite_coordinate N ℂ n r).1
    (cover_coordinate_differential_ne_zero N n r) hω D
  rw [heq] at hidx
  have hin := (indexOfSpecialty_eq_of_genusReached hmax D).2
  rw [hidx] at hin
  omega

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
