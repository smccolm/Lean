import Dubon2026.SourceOriginalSupportBottomBounds
import Dubon2026.SourceOriginalSupportBottomOdd
import Dubon2026.SourceOriginalIntegralCMDimensionData

/-! DUB-17/18 -> original CM deformation dimension. The actual original
finite linear bounds survive the same support and bottom restrictions, so the
constructed original integral multiplier and ring have full-adjoint vanishing
and the exact native cotangent dimension on the same genuine CM field. -/
namespace Dubon2026.SourceDickson
noncomputable section
open NumberField Algebra Matrix IsLocalRing
open scoped NumberField

/-- Preserve the original rational scalar structure. -/
private local instance originalIntegralCMDimensionFieldAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

/-- The actual rational bottom field is totally real. -/
private local instance originalIntegralCMDimensionFieldReal (a : 𝓞 ℚ) :
    IsTotallyReal (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) :=
  IsTotallyReal.ofRingEquiv (IntermediateField.botEquiv ℚ (rationalUnramifiedExtension a)).symm.toRingEquiv

variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
  (a : 𝓞 ℚ) (p : ℕ) [Fact p.Prime] [CharP (ResidueField O) p]
  (ha4 : (4 * a : 𝓞 ℚ) ≠ 0) (hp4 : (p : 𝓞 ℚ) ∣ 4 * a)
  (ρi : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) O)
  (ρr : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) (ResidueField O))
  (hρr : Continuous ρr)
  (C : IntermediateField (⊥ : IntermediateField ℚ (rationalUnramifiedExtension (4 * a)))
    (rationalUnramifiedExtension (4 * a)))
  [IsQuadraticExtension (⊥ : IntermediateField ℚ (rationalUnramifiedExtension (4 * a))) C]
  [IsTotallyComplex C]

/-- The exact original integral CM deformation dimension family on one genuine field
inside enlarged support. This merely names the existing literal conclusion. -/
def OriginalIntegralCMDimensionFieldData : Prop :=
  let π := (rationalArithmeticSupportRestriction a (4 * a) (dvd_mul_left a 4)).comp
    (originalRationalBottomRestriction (4 * a))
  let ρib := ρi.comp π.toMonoidHom
  let ρrb : finiteBaseArithmeticGaloisGroup (4 * a)
      (⊥ : IntermediateField ℚ (rationalUnramifiedExtension (4 * a))) →ₜ*
      GeneralLinearGroup (Fin 2) (ResidueField O) :=
    (show rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup (Fin 2) (ResidueField O)
      from ⟨ρr, hρr⟩).comp π
  ∃ hodd : (ρrb (finiteBaseRealConjugation (4 * a) ⊥)).val.det = -1,
  ∀ n : ℕ, ∀ hn : 2 * n < p - 1,
  OriginalIntegralCMSymmetricDimensionData (4 * a) ⊥ C p n (by omega) ρib ρrb hodd ha4 hp4

/-- The original integral reduction and cyclotomic determinant supply all
native ring and cotangent dimension data on this field without a new multiplier or oddness assumption. -/
theorem original_integral_cm_dimension_field_data [NoZeroDivisors O]
    (w : ℕ) (hp3 : 3 < p) (hpa : (p : 𝓞 ℚ) ∣ a) (hw : Odd w)
    (j : ResidueField O →+* K p)
    (hfinite : HasFiniteLinearSubfieldBounds p j ρr)
    (hred : ∀ g i j, (ρr g).val i j = residue O ((ρi g).val i j))
    (hdet : GeneralLinearGroup.det.comp ρr =
      (sourceArithmeticCyclotomicUnitCharacter (F := ResidueField O) p a hpa).toMonoidHom ^ w) :
    OriginalIntegralCMDimensionFieldData a p ha4 hp4 ρi ρr hρr C := by
  let π := (rationalArithmeticSupportRestriction a (4 * a) (dvd_mul_left a 4)).comp
    (originalRationalBottomRestriction (4 * a))
  let ρib := ρi.comp π.toMonoidHom
  let ρrb : finiteBaseArithmeticGaloisGroup (4 * a)
      (⊥ : IntermediateField ℚ (rationalUnramifiedExtension (4 * a))) →ₜ*
      GeneralLinearGroup (Fin 2) (ResidueField O) :=
    (show rationalArithmeticGaloisGroup a →ₜ* GeneralLinearGroup (Fin 2) (ResidueField O)
      from ⟨ρr, hρr⟩).comp π
  have hodd : (ρrb (finiteBaseRealConjugation (4 * a) ⊥)).val.det = -1 :=
    original_support_bottom_cyclotomic_odd a p w hpa hw ρr hρr hdet
  have hb : HasFiniteLinearSubfieldBounds p j ρrb.toMonoidHom :=
    original_support_bottom_finite_linear_bounds a p j ρr hfinite
  refine ⟨hodd, ?_⟩
  intro n hn
  exact original_integral_cm_symmetric_dimension_data (4 * a) ⊥ C p n (by omega)
    ρib ρrb hodd ha4 hp4 hp3 hn j hb (fun g i j => hred (π g) i j)

end
end Dubon2026.SourceDickson
