import Dubon2026.SourceCurveRationalCoordinateReciprocity
import Dubon2026.SourceCurveRationalDivisorConstants
import Dubon2026.SourceOriginalRationalCoordinate
import Dubon2026.SourceCurveFiniteCoordinateResidues

/-! DUB-17/18 -> Kummer-cover nondegeneracy -> actual cover reciprocity.
Finite-coordinate exchange gives the rational subfield of any nonconstant
function. The constant case uses principal degree zero. This transfers the
existing norm argument without a general scheme or tame-symbol construction. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (t : F) [FiniteDimensional K⟮t⟯ F]
include t

theorem finite_coordinate_ratfunc_hom_finite (φ : RatFunc K →ₐ[K] F) :
    φ.toRingHom.Finite := by
  have ht : Transcendental K (φ RatFunc.X) := by
    intro h
    exact RatFunc.transcendental_X ((isAlgebraic_algHom_iff φ φ.injective).mp h)
  haveI := finite_over_transcendental_of_finite_coordinate t ht
  exact finite_hom_of_finite_image_coordinate φ RatFunc.X

variable [IsAlgClosed K] [CharZero K] [HasPrincipalDivisors K F]

theorem finite_coordinate_weil_reciprocity
    (hres : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (f g : F) (hf : f ≠ 0) (hg : g ≠ 0) (Df Dg : Divisor K F)
    (hDf : ∀ v, Df v = v.ord f) (hDg : ∀ v, Dg v = v.ord g)
    (hdisj : ∀ v : Place K F, v.ord f ≠ 0 → v.ord g = 0) :
    rationalDivisorEval hres f Dg = rationalDivisorEval hres g Df := by
  classical
  by_cases hc : g ∈ Set.range (algebraMap K F)
  · obtain ⟨c, rfl⟩ := hc
    have he : Dg = 0 := by
      ext v
      rw [hDg, v.ord_algebraMap]
      rfl
    obtain ⟨D, hD, hd⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
    have heq : D = Df := by ext v; rw [hD, hDf]
    rw [heq] at hd
    rw [he, rationalDivisorEval_zero,
      rationalDivisorEval_constant_degree_zero hres c (fun hz => hg (by rw [hz, map_zero])) Df hd]
  · have ht : Transcendental K g := by
      intro ha
      have hm := mem_algebraicClosure_iff.mpr ha
      rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure K F)] at hm
      exact hc (IntermediateField.mem_bot.mp hm)
    let φ := rationalCoordinate g ht
    have hφ : φ RatFunc.X = g := rationalCoordinate_X g ht
    letI := algebraAlong φ
    haveI := scalarTower_along φ
    haveI : Module.Finite (RatFunc K) F := finite_coordinate_ratfunc_hom_finite t φ
    haveI : Algebra.IsSeparable (RatFunc K) F := Algebra.IsSeparable.of_integral _ _
    have hmap : algebraMap (RatFunc K) F RatFunc.X = g := hφ
    have heF : rationalExtensionPrincipalDivisor K F f = Df := by
      ext v
      exact (hDf v).symm
    have heG : rationalExtensionPrincipalDivisor K F
        (algebraMap (RatFunc K) F RatFunc.X) = Dg := by
      ext v
      rw [rationalExtensionPrincipalDivisor_apply, hmap, hDg]
    have hd : ∀ v : Place K F, v.ord f ≠ 0 →
        v.ord (algebraMap (RatFunc K) F RatFunc.X) = 0 := by
      simpa only [hmap] using hdisj
    have hr := rationalExtension_coordinate_weil_reciprocity K F f hf hd
    rw [heF, heG, hmap] at hr
    exact hr

end
end Dubon2026.SourceCurve
