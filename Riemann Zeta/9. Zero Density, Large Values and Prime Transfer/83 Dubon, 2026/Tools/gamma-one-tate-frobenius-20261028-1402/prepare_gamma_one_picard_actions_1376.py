from pathlib import Path
p=Path(__file__).parent
def out(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
out('SourceGammaOneReductionPicardEquivariance1376a.lean','''import SourceGammaOneSpecializationEquivariance
import SourceGammaOneResiduePicard1375a
import Dubon2026.SourceGammaOneHeckeArithmetic

/-! DUB-17/18 -> original Gamma1 Tate Frobenius -> the actual residue
Picard action. The proved specialization-place equivariance extends by
finite additivity to divisors and descends through the actual Picard quotient.
The same constructed reduction retains invertible-torsion injectivity.
Coordinate-degree and genus preservation remain the geometric inputs. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve IntermediateField CongruenceSubgroup
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (M : ℕ) [NeZero M]
local notation "Γ" => Gamma1 M
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => functionFieldOver Γ Qbar
local notation "Fb" => residueImage A Γ

omit [NeZero M] in
theorem reduction_arithmeticDivisor_equivariant
    (R : ConstantReduction A FF Fb) (d : A.decompositionSubgroup ℚ)
    (hplace : ∀ P : Place Qbar FF,
      R.placeMap (arithmeticPlace Γ d.val P) = decompositionResiduePlace A Γ d (R.placeMap P))
    (D : Divisor Qbar FF) :
    R.divMap (arithmeticDivisorEquiv Γ d.val D) =
      decompositionResidueDivisorEquiv A Γ d (R.divMap D) := by
  induction D using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add P n D _ _ ih =>
    simp only [map_add, ih]
    congr 1
    change Finsupp.mapDomain R.placeMap
        (Finsupp.equivMapDomain (arithmeticPlaceEquiv Γ d.val) (Finsupp.single P n)) =
      Finsupp.equivMapDomain (decompositionResiduePlaceEquiv A Γ d)
        (Finsupp.mapDomain R.placeMap (Finsupp.single P n))
    rw [Finsupp.equivMapDomain_single, Finsupp.mapDomain_single,
      Finsupp.mapDomain_single, Finsupp.equivMapDomain_single]
    exact congrArg (fun Q => Finsupp.single Q n) (hplace P)

theorem reduction_arithmeticPicard_equivariant
    (R : ConstantReduction A FF Fb) (d : A.decompositionSubgroup ℚ)
    (hplace : ∀ P : Place Qbar FF,
      R.placeMap (arithmeticPlace Γ d.val P) = decompositionResiduePlace A Γ d (R.placeMap P))
    (x : Pic0 Qbar FF) :
    R.pic0Map (gamma1ArithmeticPicardRep Qbar M d.val x) =
      decompositionResiduePicard A Γ (by simp [Gamma1_mem, ModularGroup.T]) d (R.pic0Map x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  have hT : ModularGroup.T ∈ Γ := by simp [Gamma1_mem, ModularGroup.T]
  change Pic0.mk (R.degZeroMap (arithmeticDegZero Γ hT d.val D)) =
    decompositionResiduePicard A Γ hT d (Pic0.mk (R.degZeroMap D))
  rw [decompositionResiduePicard_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact reduction_arithmeticDivisor_equivariant A M R d hplace D.val

theorem exists_gammaOne_reduction_picard_equivariant_of_degree_genus_eq
    (hdeg : Module.finrank Qbar⟮jCoordinateOver Γ Qbar⟯ FF =
      Module.finrank kk⟮residueJCoordinate A Γ⟯ Fb)
    (hgen : genusFF kk Fb = genusFF Qbar FF) :
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = regularProlongation A Γ ∧
      (∀ m : ℕ, (m : kk) ≠ 0 → Set.InjOn R.pic0Map (↑(Pic0.torsion (K := Qbar) (F := FF) m))) ∧
      ∀ (d : A.decompositionSubgroup ℚ) (x : Pic0 Qbar FF),
        R.pic0Map (gamma1ArithmeticPicardRep Qbar M d.val x) =
          decompositionResiduePicard A Γ (by simp [Gamma1_mem, ModularGroup.T]) d (R.pic0Map x) := by
  obtain ⟨R, hR, hinj, hplace⟩ :=
    exists_gammaOne_reduction_decomposition_equivariant_of_degree_genus_eq A M hdeg hgen
  exact ⟨R, hR, hinj, fun d x => reduction_arithmeticPicard_equivariant A M R d (hplace d) x⟩

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
''')
out('SourceGammaOneNormDiamondOrientation1377a.lean','''import Dubon2026.SourceGammaOneDiamondPicard

/-! DUB-17/18 -> original Gamma1 Frobenius characteristic relation ->
exact diamond normalization. The norm uses the field diamond with label
p-inverse. The original Picard convention uses the inverse field action,
so the corresponding Picard diamond is the inverse matrix lift, with label
p. These identifications retain the source convention and prove the inverse. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
variable (M : ℕ) [NeZero M]
local notation "FF" => functionFieldOver (Gamma1 M) Qbar

theorem arithmeticDiamondAut_inverse_lift (g : Gamma0 M) :
    (ConstantField.arithmeticDiamondAut M g⁻¹).symm = ConstantField.arithmeticDiamondAut M g := by
  ext f
  change ConstantField.arithmeticDiamondHom M g⁻¹⁻¹ f = ConstantField.arithmeticDiamondHom M g f
  rw [inv_inv]

theorem norm_diamond_inverse_label (p : ℕ) (g : Gamma0 M)
    (hlabel : (p : ZMod M) * (g.val 1 1 : ZMod M) = 1) :
    ((g⁻¹).val 1 1 : ZMod M) = (p : ZMod M) := by
  have hh : (p : ZMod M) * Gamma0Map M g = 1 := hlabel
  have hi : Gamma0Map M g * Gamma0Map M g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  change Gamma0Map M g⁻¹ = (p : ZMod M)
  calc
    Gamma0Map M g⁻¹ = 1 * Gamma0Map M g⁻¹ := (one_mul _).symm
    _ = ((p : ZMod M) * Gamma0Map M g) * Gamma0Map M g⁻¹ := by rw [hh]
    _ = (p : ZMod M) := by rw [mul_assoc, hi, mul_one]

theorem arithmeticDiamondPicard_inverse_lift_mk (g : Gamma0 M)
    (D : Divisor.degZero (K := Qbar) (F := FF)) :
    arithmeticDiamondPicard M g⁻¹ (Pic0.mk D) =
      Pic0.mk (fieldDegZeroEquiv (ConstantField.arithmeticDiamondAut M g)
        (functionFieldOver_residue_bijective (Gamma1 M) (by simp [Gamma1_mem, ModularGroup.T]))
        (functionFieldOver_residue_bijective (Gamma1 M) (by simp [Gamma1_mem, ModularGroup.T])) D) := by
  rw [arithmeticDiamondPicard_mk, arithmeticDiamondAut_inverse_lift]

end
end Dubon2026.SourceFunctionField.GammaOne
''')
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceGammaOneReductionPicardEquivariance1376a','SourceGammaOneNormDiamondOrientation1377a')")
out('build_gamma_one_picard_actions_1376.ps1',s)
