import Dubon2026.SourceCurveSeparatingCoordinateCanonical
import Dubon2026.SourceCurveTateCanonicalSupport
import Dubon2026.SourceCurveGlobalTateTrace
import Dubon2026.SourceCurveAdjoinGeneratorResidues

/-! DUB-17/18 -> original all-weight association -> homogeneous Gamma1
realization -> original genus preservation -> reverse genus -> residue Hurwitz
and canonical degree. Native global Tate trace already accepts every finite
separable extension. The proved finite differential support and local generation
therefore reduce the actual global residue sum to the existing rational-field
residue theorem in every characteristic. No global vanishing premise is retained. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField KaehlerDifferential
variable {K F : Type*} [Field K] [IsAlgClosed K]
  [Field F] [Algebra K F]
variable (t : F) [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F]

theorem separating_coordinate_tate_support
    (ht : Transcendental K t) (hDt : D K F t ≠ 0) (f : F) :
    (Function.support (fun v : Place K F => v.tateResidue f t)).Finite := by
  letI : Nontrivial Ω[F⁄K] := nontrivial_of_ne _ _ hDt
  letI : ∀ v : Place K F, v.DCoordGenerates := separating_coordinate_place_dCoordGenerates t ht hDt
  exact tateResidue_support_finite
    (fun v => v.canonicalLocalResidueData (place_residue_bijective_of_finite_coordinate t v).2)
    (place_residue_bijective_of_finite_coordinate t) f t
    (finite_function_support_of_separating_coordinate t ht f)
    (separating_coordinate_D_support t ht hDt)

theorem separating_coordinate_global_tateResidue_zero
    (ht : Transcendental K t) (hDt : D K F t ≠ 0) (f : F) :
    (∑ᶠ v : Place K F, v.tateResidue f t) = 0 := by
  let J := K⟮t⟯
  have h := tateResidue_global_trace (F := J)
    (place_residue_bijective_of_finite_coordinate t) f (AdjoinSimple.gen K t)
    (separating_coordinate_tate_support t ht hDt f)
  exact h.trans (sum_tateResidue_adjoin_generator_eq_zero t ht (Algebra.trace J F f))

theorem separating_coordinate_global_residue_sum_zero
    (ht : Transcendental K t) (hDt : D K F t ≠ 0)
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K]) (f : F) :
    (∑ᶠ v : Place K F, kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v) = 0 := by
  letI := isCurveOver_separating_coordinate t ht hDt
  letI : Nontrivial Ω[F⁄K] := nontrivial_of_ne _ _ hDt
  letI : ∀ v : Place K F, v.DCoordGenerates := separating_coordinate_place_dCoordGenerates t ht hDt
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
    _ = 0 := separating_coordinate_global_tateResidue_zero t ht hDt (f * c)

end
end Dubon2026.SourceCurve
