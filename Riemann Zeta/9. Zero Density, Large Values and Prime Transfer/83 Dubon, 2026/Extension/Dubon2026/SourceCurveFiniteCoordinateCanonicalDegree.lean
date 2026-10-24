import Dubon2026.SourceCurveFiniteCoordinateResidueDuality
import Dubon2026.SourceCurveRepartitionIndex

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer-cover genus.
The proved residue duality and degree-dimension maximum identify the
actual canonical degree with twice the source H1 genus minus two.
This is applied to the actual finite modular extension downstream;
the unramified pullback calculation remains a separate obligation. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField KaehlerDifferential
variable {K F : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Field F] [Algebra K F]
variable (t : F) [FiniteDimensional K⟮t⟯ F]

theorem finite_coordinate_canonical_degree_eq_genusFF
    (ht : Transcendental K t) (hDt : D K F t ≠ 0) :
    letI := hasCanonicalDivisor_finite_coordinate t ht hDt
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0),
      Divisor.degree (canonicalDivisorOf hω) = 2 * (genusFF K F : ℤ) - 2 := by
  letI := hasCanonicalDivisor_finite_coordinate t ht hDt
  letI := hasPrincipalDivisors_closed_of_separating_coordinate t ht
  letI : ∀ v : Place K F, Module.Finite K v.ResidueField := finite_coordinate_place_residue t
  obtain ⟨P⟩ := nonempty_place_of_separating_coordinate t ht
  letI := finite_lSpace_zero_of_place P
  have hz : ell (0 : Divisor K F) = 1 := finrank_lSpace_zero_of_principalDivisors P
  obtain ⟨γ, D₀, h⟩ := finite_coordinate_degree_dimension_maximum t ht
  intro ω hω
  have hi0 := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [hz, Nat.cast_one, map_zero] at hi0
  have hiK := (indexOfSpecialty_eq_of_genusReached h (canonicalDivisorOf hω)).2
  have heK := finite_coordinate_index_eq_canonical_complement t ht hDt hω 0
  rw [sub_zero] at heK
  have hiK1 := finite_coordinate_index_eq_canonical_complement t ht hDt hω
    (canonicalDivisorOf hω)
  rw [sub_self, hz] at hiK1
  rw [genusFF_eq_zero_index]
  omega

end
end Dubon2026.SourceCurve
