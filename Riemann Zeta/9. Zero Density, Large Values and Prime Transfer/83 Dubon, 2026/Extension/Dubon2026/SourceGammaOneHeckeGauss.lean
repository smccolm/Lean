import Dubon2026.SourceGammaOneRegularProlongation
import Dubon2026.SourceGammaOneHeckeDegeneracy

/-! DUB-17/18 -> original Gamma1 geometric Frobenius quadratic -> reduction
of the actual Hecke correspondence. Both original field maps preserve the
literal coefficient valuation. Their residue maps are inclusion and the
original substitution q to q^d. Reuse native coefficient/substitution
commutation and fraction witnesses, without good-reduction assumptions.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open GaussReduction CongruenceSubgroup
variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
  (M d : ℕ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Γ" => Gamma1 M
local notation "Δ" => Gamma1 M ⊓ Gamma0 (d * M)

theorem heckeAlpha_mem_gaussRing (f : coefficientGaussRing Γ A) :
    heckeAlpha L M d f.val ∈ coefficientGaussRing Δ A := by
  change IsInt A (heckeAlpha L M d f.val : LaurentSeries L)
  rw [heckeAlpha_coe]
  exact f.property

/-- The original first Hecke field map restricted to integral functions. -/
def heckeAlphaGauss : coefficientGaussRing Γ A →+* coefficientGaussRing Δ A :=
  (((heckeAlpha L M d).toRingHom).comp (coefficientGaussRing Γ A).subtype).codRestrict
    (coefficientGaussRing Δ A).toSubring (heckeAlpha_mem_gaussRing A M d)

theorem heckeAlphaGauss_resHom (f : coefficientGaussRing Γ A) :
    resHom A Δ (heckeAlphaGauss A M d f) = resHom A Γ f := by
  obtain ⟨hy, h⟩ := wit_spec A Γ f
  have h' : ((heckeAlphaGauss A M d f : functionFieldOver Δ L) : LaurentSeries L) *
      ι A (wit A Γ f).2 = ι A (wit A Γ f).1 := by
    change (heckeAlpha L M d f.val : LaurentSeries L) * ι A (wit A Γ f).2 = _
    rw [heckeAlpha_coe]
    exact h
  rw [resHom_eq A Δ hy h', resHom_eq A Γ hy h]

variable [NeZero d]

omit M [Algebra ℚ L] in
theorem isInt_qExpand {f : LaurentSeries L} (hf : IsInt A f) :
    IsInt A (qExpand L d f) := by
  obtain ⟨x, y, hy, h⟩ := hf
  refine ⟨qExpand A d x, qExpand A d y, ?_, ?_⟩
  · change coeffMap (IsLocalRing.residue A) (qExpand A d y) ≠ 0
    rw [coeffMap_qExpand]
    exact (map_ne_zero _).mpr hy
  · change qExpand L d f * coeffMap A.subtype (qExpand A d y) =
      coeffMap A.subtype (qExpand A d x)
    rw [coeffMap_qExpand, coeffMap_qExpand, ← map_mul]
    exact congrArg (qExpand L d) h

theorem heckeBeta_mem_gaussRing (f : coefficientGaussRing Γ A) :
    heckeBeta L M d f.val ∈ coefficientGaussRing Δ A := by
  change IsInt A (heckeBeta L M d f.val : LaurentSeries L)
  rw [heckeBeta_coe]
  exact isInt_qExpand A d f.property

/-- The original q-substitution Hecke field map restricted to integral functions. -/
def heckeBetaGauss : coefficientGaussRing Γ A →+* coefficientGaussRing Δ A :=
  (((heckeBeta L M d).toRingHom).comp (coefficientGaussRing Γ A).subtype).codRestrict
    (coefficientGaussRing Δ A).toSubring (heckeBeta_mem_gaussRing A M d)

theorem heckeBetaGauss_resHom (f : coefficientGaussRing Γ A) :
    resHom A Δ (heckeBetaGauss A M d f) = qExpand kk d (resHom A Γ f) := by
  obtain ⟨hy, h⟩ := wit_spec A Γ f
  have hy' : ϖ A (qExpand A d (wit A Γ f).2) ≠ 0 := by
    rw [show ϖ A (qExpand A d (wit A Γ f).2) = qExpand kk d (ϖ A (wit A Γ f).2) from
      coeffMap_qExpand (IsLocalRing.residue A) d _]
    exact (map_ne_zero _).mpr hy
  have h' : ((heckeBetaGauss A M d f : functionFieldOver Δ L) : LaurentSeries L) *
      ι A (qExpand A d (wit A Γ f).2) = ι A (qExpand A d (wit A Γ f).1) := by
    change qExpand L d (f.val : LaurentSeries L) *
      coeffMap A.subtype (qExpand A d (wit A Γ f).2) =
        coeffMap A.subtype (qExpand A d (wit A Γ f).1)
    rw [coeffMap_qExpand, coeffMap_qExpand, ← map_mul]
    exact congrArg (qExpand L d) h
  rw [resHom_eq A Δ hy' h', resHom_eq A Γ hy h, map_div₀]
  change coeffMap (IsLocalRing.residue A) (qExpand A d (wit A Γ f).1) /
      coeffMap (IsLocalRing.residue A) (qExpand A d (wit A Γ f).2) = _
  rw [coeffMap_qExpand, coeffMap_qExpand]

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
