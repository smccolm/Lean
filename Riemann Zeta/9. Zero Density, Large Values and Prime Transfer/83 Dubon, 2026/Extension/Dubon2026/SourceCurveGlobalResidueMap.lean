import Dubon2026.SourceCurveResidueFunctional

/-! DUB-17/18 -> global residue identity -> finite Galois averaging.
A fixed actual differential and the proved finite supports of its order and
of principal orders suffice to make its residue sum a linear functional on
global functions. This avoids building a separate adelic or Riemann--Roch
package for the auxiliary normal closure. No residue vanishing is assumed.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem diagonal_residue_support_finite
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K])
    (f : F) (hf : {v : Place K F | v.ord f ≠ 0}.Finite)
    (hω : {v : Place K F | v.ordDifferential ω ≠ 0}.Finite) :
    (Function.support (kaehlerResidueTermKFam Rfam ω (diagonalHom K F f))).Finite := by
  refine (hf.union hω).subset ?_
  intro v hv
  by_contra hn
  have hnf : v.ord f = 0 := not_not.mp (not_or.mp hn).1
  have hnω : v.ordDifferential ω = 0 := not_not.mp (not_or.mp hn).2
  apply hv
  apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg
  change f * v.differentialCoeff ω = 0 ∨ 0 ≤ v.ord (f * v.differentialCoeff ω)
  rcases eq_or_ne f 0 with rfl | hf0
  · exact Or.inl (zero_mul _)
  rcases eq_or_ne (v.differentialCoeff ω) 0 with h0 | h0
  · exact Or.inl (by rw [h0, mul_zero])
  right
  rw [v.ord_mul hf0 h0, hnf]
  change 0 ≤ 0 + v.ordDifferential ω
  simp only [hnω, zero_add, le_refl]

/-- The actual finite local-residue sum of a fixed differential on global functions. -/
def globalResidueLinearMap
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K])
    (hfun : ∀ f : F, {v : Place K F | v.ord f ≠ 0}.Finite)
    (hω : {v : Place K F | v.ordDifferential ω ≠ 0}.Finite) : F →ₗ[K] K where
  toFun f := ∑ᶠ v, kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v
  map_add' f g := by
    rw [← finsum_add_distrib (diagonal_residue_support_finite Rfam ω f (hfun f) hω)
      (diagonal_residue_support_finite Rfam ω g (hfun g) hω)]
    apply finsum_congr
    intro v
    simp only [kaehlerResidueTermKFam_apply]
    change Algebra.trace K v.ResidueField ((Rfam v).res ((f + g) * v.differentialCoeff ω)) = _
    rw [add_mul, map_add, map_add]
    rfl
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [smul_finsum]
    apply finsum_congr
    intro v
    simp only [kaehlerResidueTermKFam_apply]
    change Algebra.trace K v.ResidueField ((Rfam v).res ((c • f) * v.differentialCoeff ω)) = _
    rw [Algebra.smul_def, mul_assoc, ← Algebra.smul_def, map_smul, map_smul]
    rfl

theorem globalResidueLinearMap_apply
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K])
    (hfun : ∀ f : F, {v : Place K F | v.ord f ≠ 0}.Finite)
    (hω : {v : Place K F | v.ordDifferential ω ≠ 0}.Finite) (f : F) :
    globalResidueLinearMap Rfam ω hfun hω f =
      ∑ᶠ v, kaehlerResidueTermKFam Rfam ω (diagonalHom K F f) v := rfl

end
end Dubon2026.SourceCurve
