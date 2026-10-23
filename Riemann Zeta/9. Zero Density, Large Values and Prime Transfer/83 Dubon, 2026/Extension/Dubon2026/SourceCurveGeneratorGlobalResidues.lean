import Dubon2026.SourceCurveGeneratorPowerResidues
import Dubon2026.SourceCurveTateGlobalFunctional
import Dubon2026.SourceRationalShiftPowerSpan

/-! The global residue against a generator of an actual rational field
vanishes in every characteristic. Shifted powers span the field by the
proved partial-fraction theorem. Their residue sums are the already proved
zero signed-order sums. This is the rational base case for DUB-17/18. -/

noncomputable section

namespace Dubon2026.SourceCurve

open IntermediateField

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]

omit [IsAlgClosed K] in
/-- Subtracting a constant preserves an actual rational-field generator. -/
theorem adjoin_generator_sub_const (t : F) (hgen : K⟮t⟯ = ⊤) (c : K) :
    K⟮t - algebraMap K F c⟯ = ⊤ := by
  apply top_le_iff.mp
  rw [← hgen]
  apply adjoin_simple_le_iff.mpr
  have h := add_mem
    (mem_adjoin_simple_self K (t - algebraMap K F c))
    ((K⟮t - algebraMap K F c⟯).algebraMap_mem c)
  simpa only [sub_add_cancel] using h

/-- The actual global residue against a rational generator vanishes for every function. -/
theorem sum_tateResidue_generator_eq_zero (t : F) (ht : Transcendental K t)
    (hgen : K⟮t⟯ = ⊤) (f : F) :
    (∑ᶠ v : Place K F, v.tateResidue f t) = 0 := by
  obtain ⟨hfinite, hsep⟩ := finite_separable_of_adjoin_eq_top t hgen
  have hres (v : Place K F) :=
    (place_residue_bijective_of_finite_coordinate t v).surjective
  have hfun (g : F) := finite_function_support_of_separating_coordinate t ht g
  let φ := globalTateFunctional hres hfun t
  let e := rationalCoordinateEmbedding K t ht
  have hsurj : Function.Surjective e := by
    intro g
    let z : K⟮t⟯ := ⟨g, hgen ▸ mem_top⟩
    refine ⟨(RatFunc.algEquivOfTranscendental t ht).symm z, ?_⟩
    change ((RatFunc.algEquivOfTranscendental t ht
      ((RatFunc.algEquivOfTranscendental t ht).symm z) : K⟮t⟯) : F) = g
    rw [AlgEquiv.apply_symm_apply]
  have hφ : φ.comp e.toLinearMap = 0 := by
    apply linearMap_eq_zero_of_shift_powers K
    intro c n
    change φ (e ((RatFunc.X - RatFunc.C c) ^ n)) = 0
    rw [map_zpow₀, map_sub, rationalCoordinateEmbedding_X]
    change φ ((t - e (algebraMap K (RatFunc K) c)) ^ n) = 0
    rw [e.commutes]
    change (∑ᶠ v : Place K F, v.tateResidue ((t - algebraMap K F c) ^ n) t) = 0
    have htc : Transcendental K (t - algebraMap K F c) := by
      intro ha
      apply ht
      simpa only [sub_add_cancel] using ha.add (isAlgebraic_algebraMap c)
    calc
      _ = ∑ᶠ v : Place K F,
          v.tateResidue ((t - algebraMap K F c) ^ n) (t - algebraMap K F c) := by
        apply finsum_congr
        intro v
        have hv := v.tateResidue_add_algebraMap (hres v)
          ((t - algebraMap K F c) ^ n) (t - algebraMap K F c) c
        simpa only [sub_add_cancel] using hv
      _ = 0 := sum_generator_tateResidue_zpow _ htc (adjoin_generator_sub_const t hgen c) n
  obtain ⟨g, rfl⟩ := hsurj f
  exact LinearMap.congr_fun hφ g

/-- The literal rational function field satisfies global residue vanishing against its coordinate. -/
theorem rational_sum_tateResidue_X_eq_zero (K : Type*) [Field K] [IsAlgClosed K]
    (f : RatFunc K) :
    (∑ᶠ v : Place K (RatFunc K), v.tateResidue f RatFunc.X) = 0 :=
  sum_tateResidue_generator_eq_zero RatFunc.X RatFunc.transcendental_X RatFunc.adjoin_X f

end Dubon2026.SourceCurve
