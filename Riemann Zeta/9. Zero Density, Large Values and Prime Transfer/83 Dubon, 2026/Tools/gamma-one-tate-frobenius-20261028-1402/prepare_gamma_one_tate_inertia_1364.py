from pathlib import Path
p=Path(__file__).parent
def out(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
header='''namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve IntermediateField
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (M : ℕ) [NeZero M]
local notation "Δ" => CongruenceSubgroup.Gamma1 M
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => functionFieldOver Δ Qbar
local notation "Fb" => residueImage A Δ

'''
hyp='''    (hdeg : Module.finrank Qbar⟮jCoordinateOver Δ Qbar⟯ FF =
      Module.finrank kk⟮residueJCoordinate A Δ⟯ Fb)
    (hgen : genusFF kk Fb = genusFF Qbar FF)
'''
end='\nend\nend Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction\n'
out('SourceGammaOneInertiaPlaceReduction1364a.lean','''import SourceGammaOneSpecializationEquivariance1363b

/-! DUB-17/18 -> original Gamma1 Tate inertia -> actual specialization
of places. The proved decomposition equivariance and trivial residue inertia
action give invariance of the same specialization that is injective on
invertible Picard torsion. Degree and genus preservation remain explicit. -/
'''+header+'''theorem exists_gammaOne_reduction_invariant_on_inertia_of_degree_genus_eq
'''+hyp+'''    : ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = regularProlongation A Δ ∧
      (∀ m : ℕ, (m : kk) ≠ 0 →
        Set.InjOn R.pic0Map (↑(Pic0.torsion (K := Qbar) (F := FF) m))) ∧
      ∀ τ : Qbar ≃ₐ[ℚ] Qbar,
        τ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype →
        ∀ P : Place Qbar FF, R.placeMap (arithmeticPlace Δ τ P) = R.placeMap P := by
  obtain ⟨R, hR, hinj, hplace⟩ :=
    exists_gammaOne_reduction_decomposition_equivariant_of_degree_genus_eq A M hdeg hgen
  refine ⟨R, hR, hinj, ?_⟩
  intro τ hτ P
  obtain ⟨d, hd, rfl⟩ := hτ
  rw [hplace, decompositionResiduePlace_eq_self_of_inertia A Δ d hd]
'''+end)
out('SourceGammaOneInertiaPicard1365a.lean','''import SourceGammaOneInertiaPlaceReduction1364a
import Dubon2026.SourceGammaOneHeckeArithmetic

/-! DUB-17/18 -> original Gamma1 Tate inertia -> original Picard torsion.
The literal divisor pushforward carries place invariance to the actual
Picard quotient. Injectivity of the constructed specialization on invertible
torsion then proves inertia triviality on the original arithmetic action.
Only coordinate-degree and genus preservation remain geometric inputs. -/
'''+header+'''theorem reduction_arithmeticDivisor_invariant
    (R : ConstantReduction A FF Fb) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hplace : ∀ P : Place Qbar FF, R.placeMap (arithmeticPlace Δ τ P) = R.placeMap P)
    (D : Divisor Qbar FF) :
    R.divMap (arithmeticDivisorEquiv Δ τ D) = R.divMap D := by
  induction D using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add P n D _ _ ih =>
    rw [map_add, map_add, map_add, ih]
    congr 1
    change Finsupp.mapDomain R.placeMap
        (Finsupp.equivMapDomain (arithmeticPlaceEquiv Δ τ) (Finsupp.single P n)) =
      Finsupp.mapDomain R.placeMap (Finsupp.single P n)
    rw [Finsupp.equivMapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    exact congrArg (fun Q => Finsupp.single Q n) (hplace P)

theorem reduction_arithmeticPicard_invariant
    (R : ConstantReduction A FF Fb) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hplace : ∀ P : Place Qbar FF, R.placeMap (arithmeticPlace Δ τ P) = R.placeMap P)
    (x : Pic0 Qbar FF) :
    R.pic0Map (gamma1ArithmeticPicardRep Qbar M τ x) = R.pic0Map x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  have hT : ModularGroup.T ∈ Δ := by simp [CongruenceSubgroup.Gamma1_mem, ModularGroup.T]
  change R.pic0Map (Pic0.mk (arithmeticDegZero Δ hT τ D)) = R.pic0Map (Pic0.mk D)
  rw [ConstantReduction.pic0Map_mk, ConstantReduction.pic0Map_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact reduction_arithmeticDivisor_invariant A M R τ hplace D.val

theorem gammaOne_arithmeticPicard_eq_self_of_inertia_of_degree_genus_eq
'''+hyp+'''    (m : ℕ) (hm : (m : kk) ≠ 0) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hτ : τ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype)
    (x : Pic0 Qbar FF) (hx : x ∈ Pic0.torsion m) :
    gamma1ArithmeticPicardRep Qbar M τ x = x := by
  obtain ⟨R, _, hinj, hplace⟩ :=
    exists_gammaOne_reduction_invariant_on_inertia_of_degree_genus_eq A M hdeg hgen
  apply hinj m hm (gamma1ArithmeticPicardRep_torsion M τ m x hx) hx
  exact reduction_arithmeticPicard_invariant A M R τ (hplace τ hτ) x
'''+end)
out('SourceGammaOneTateInertia1366a.lean','''import SourceGammaOneInertiaPicard1365a
import Dubon2026.SourceGammaOneArithmeticTateOperators

/-! DUB-17/18 -> original Gamma1 arithmetic association -> inertia on the
actual Tate representation. Each native compatible sequence coordinate is
prime-power Picard torsion, so the proved original Picard inertia theorem
applies. No Tate action or geometric realization is postulated. Coordinate-
degree and genus preservation remain; this is not the two-dimensional
characteristic-zero association or the Frobenius characteristic polynomial. -/
'''+header+'''theorem gammaOne_arithmeticTateGaloisRep_eq_one_of_inertia_of_degree_genus_eq
'''+hyp+'''    (ell : ℕ) [Fact ell.Prime] (hell : (ell : kk) ≠ 0)
    (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hτ : τ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype) :
    arithmeticTateGaloisRep M ell τ = 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change gamma1ArithmeticPicardRep Qbar M τ ((x : ℕ → Pic0 Qbar FF) n) =
    (x : ℕ → Pic0 Qbar FF) n
  apply gammaOne_arithmeticPicard_eq_self_of_inertia_of_degree_genus_eq A M hdeg hgen
    (ell ^ n) (by simpa only [Nat.cast_pow] using pow_ne_zero n hell) τ hτ
  apply Pic0.mem_torsion_iff.mpr
  rw [← Nat.cast_smul_eq_nsmul ℤ]
  exact TateModule.torsion x n
'''+end)
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceGammaOneInertiaPlaceReduction1364a','SourceGammaOneInertiaPicard1365a','SourceGammaOneTateInertia1366a')")
out('build_gamma_one_tate_inertia_1364.ps1',s)
print('Prepared original Picard and Tate inertia consumers.')
