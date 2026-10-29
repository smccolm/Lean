import Dubon2026.SourceGammaOneResidueArithmetic
import Dubon2026.SourceGammaOneResidueHeckeFinite
import Dubon2026.SourceLaurentFrobenius

/-! DUB-17/18 -> original Gamma1 Frobenius quadratic -> the geometric
residue component. For an original arithmetic Frobenius element, inverse
coefficient action followed by the pth power is the literal substitution
q to q^p on the actual residue field. The original second Hecke map factors
through this endomorphism and the original first map. No norm/product,
degree preservation, genus or Picard specialization is asserted here.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => residueImage A Γ

theorem decompositionResidueAut_symm_constants (d : A.decompositionSubgroup ℚ) (a : kk) :
    (decompositionResidueAut A Γ d).symm (algebraMap kk Fb a) =
      algebraMap kk Fb (d⁻¹ • a) := by
  apply Subtype.ext
  change coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d⁻¹)
      (algebraMap kk (LaurentSeries kk) a) = algebraMap kk (LaurentSeries kk) (d⁻¹ • a)
  simpa only [SourceDifferential.algebraMap_laurentSeries_apply_alt] using
    coeffMap_single (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d⁻¹) 0 a

variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
  (d : A.decompositionSubgroup ℚ) (hd : ∀ a : IsLocalRing.ResidueField A, d • a = a ^ p)

/-- Geometric Frobenius on the actual residue image, with its original Laurent coordinate. -/
def geometricFrobenius : Fb →ₐ[kk] Fb :=
  { (frobenius Fb p).comp (decompositionResidueAut A Γ d).symm.toRingHom with
    commutes' := fun a => by
      change ((decompositionResidueAut A Γ d).symm (algebraMap kk Fb a)) ^ p = _
      rw [decompositionResidueAut_symm_constants, ← map_pow, ← hd, smul_inv_smul] }

theorem geometricFrobenius_coe (f : Fb) :
    (geometricFrobenius A Γ p d hd f : LaurentSeries kk) = qExpand kk p f.val := by
  change (coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d⁻¹)
      f.val) ^ p = qExpand kk p f.val
  rw [pow_char_eq_coeffMap_frobenius_qExpand, ← coeffMap_qExpand, coeffMap_coeffMap]
  have he : (frobenius kk p).comp
      (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d⁻¹) = RingHom.id kk := by
    ext a
    change (d⁻¹ • a) ^ p = a
    rw [← hd, smul_inv_smul]
  rw [he, coeffMap_id]

theorem geometricFrobenius_coefficient (f : Fb) :
    geometricFrobenius A Γ p d hd (decompositionResidueAut A Γ d f) = f ^ p := by
  change ((decompositionResidueAut A Γ d).symm (decompositionResidueAut A Γ d f)) ^ p = _
  rw [RingEquiv.symm_apply_apply]

theorem geometricFrobenius_isIntegral : (geometricFrobenius A Γ p d hd).toRingHom.IsIntegral := by
  intro f
  refine ⟨Polynomial.X ^ p - Polynomial.C (decompositionResidueAut A Γ d f),
    Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero, ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero]
  exact (geometricFrobenius_coefficient A Γ p d hd f).symm

theorem geometricFrobenius_finite [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    (geometricFrobenius A Γ p d hd).toRingHom.Finite := by
  let t := residueJCoordinate A Γ
  haveI : FiniteDimensional (IntermediateField.adjoin kk ({t} : Set Fb)) Fb :=
    (finite_residueCoordinate_and_degree_le A Γ hT).1
  have ht : Transcendental kk (geometricFrobenius A Γ p d hd t) := by
    intro h
    exact transcendental_residueJCoordinate A Γ
      ((isAlgebraic_algHom_iff (geometricFrobenius A Γ p d hd)
        (geometricFrobenius A Γ p d hd).injective).mp h)
  haveI := SourceCurve.finite_over_transcendental_of_finite_coordinate t ht
  exact SourceCurve.finite_hom_of_finite_image_coordinate (geometricFrobenius A Γ p d hd) t

omit Γ in
theorem residueHeckeAlpha_coe (M d₀ : ℕ) (f : residueImage A (Gamma1 M)) :
    (residueHeckeAlpha A M d₀ f : LaurentSeries kk) = f.val :=
  IntermediateField.coe_inclusion (residueImage_heckeAlpha_le A M d₀) f

omit Γ in
theorem residueHeckeBeta_coe (M d₀ : ℕ) [NeZero d₀]
    (f : residueImage A (Gamma1 M)) :
    (residueHeckeBeta A M d₀ f : LaurentSeries kk) = qExpand kk d₀ f.val := rfl

omit Γ in
theorem residueHeckeBeta_eq_alpha_geometricFrobenius (M : ℕ)
    (f : residueImage A (Gamma1 M)) :
    residueHeckeBeta A M p f = residueHeckeAlpha A M p
      (geometricFrobenius A (Gamma1 M) p d hd f) := by
  apply Subtype.ext
  rw [residueHeckeBeta_coe, residueHeckeAlpha_coe, geometricFrobenius_coe]

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
