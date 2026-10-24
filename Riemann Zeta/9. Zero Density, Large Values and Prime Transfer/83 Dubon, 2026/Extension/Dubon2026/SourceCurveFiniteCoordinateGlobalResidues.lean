import Dubon2026.SourceCurveFiniteCoordinateCanonical
import Dubon2026.SourceCurveTateCanonicalSupport
import Dubon2026.SourceCurveGlobalTateTrace
import Dubon2026.SourceCurveAdjoinGeneratorResidues

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer-cover genus ->
canonical degree -> residue duality. The existing local Tate comparison,
global trace theorem and rational-function residue theorem give global
residue vanishing for the cover's finite coordinate. No global residue
identity or completed-field decomposition is assumed. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField KaehlerDifferential
variable {K F : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Field F] [Algebra K F]
variable (t : F) [FiniteDimensional K⟮t⟯ F]

theorem finite_coordinate_tate_support
    (ht : Transcendental K t) (hDt : D K F t ≠ 0) (f : F) :
    (Function.support (fun v : Place K F => v.tateResidue f t)).Finite := by
  letI : Nontrivial Ω[F⁄K] := nontrivial_of_ne _ _ hDt
  letI : ∀ v : Place K F, v.DCoordGenerates := finite_coordinate_place_dCoordGenerates t
  exact tateResidue_support_finite
    (fun v => v.canonicalLocalResidueData (place_residue_bijective_of_finite_coordinate t v).2)
    (place_residue_bijective_of_finite_coordinate t) f t
    (finite_function_support_of_separating_coordinate t ht f)
    (finite_coordinate_D_support t ht hDt)

theorem finite_coordinate_global_tateResidue_zero
    (ht : Transcendental K t) (hDt : D K F t ≠ 0) (f : F) :
    (∑ᶠ v : Place K F, v.tateResidue f t) = 0 := by
  let J := K⟮t⟯
  have h := tateResidue_global_trace (F := J)
    (place_residue_bijective_of_finite_coordinate t) f (AdjoinSimple.gen K t)
    (finite_coordinate_tate_support t ht hDt f)
  exact h.trans (sum_tateResidue_adjoin_generator_eq_zero t ht (Algebra.trace J F f))

theorem finite_coordinate_global_residue_sum_zero
    (ht : Transcendental K t) (hDt : D K F t ≠ 0)
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K]) (f : F) :
    (∑ᶠ v : Place K F, kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v) = 0 := by
  letI := isCurveOver_finite_coordinate t ht hDt
  letI : Nontrivial Ω[F⁄K] := nontrivial_of_ne _ _ hDt
  letI : ∀ v : Place K F, v.DCoordGenerates := finite_coordinate_place_dCoordGenerates t
  obtain ⟨c, rfl⟩ := RegularDifferentialsComparison.exists_smul_eq hDt ω
  calc
    _ = ∑ᶠ v : Place K F, v.tateResidue (f * c) t := by
      apply finsum_congr
      intro v
      rw [v.tateResidue_eq_canonical_differential (Rfam v)
        (place_residue_bijective_of_finite_coordinate t v)]
      simp only [kaehlerResidueTermKFam_apply, v.differentialCoeff_smul]
      change Algebra.trace K v.ResidueField ((Rfam v).res
        (f * (c * v.differentialCoeff (D K F t)))) = _
      rw [← mul_assoc]
    _ = 0 := finite_coordinate_global_tateResidue_zero t ht hDt (f * c)

end
end Dubon2026.SourceCurve
