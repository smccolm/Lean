from pathlib import Path
p=Path(__file__).parent
def out(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
out('SourceGammaOneDecompositionCharts1361a.lean','''import SourceGammaOneArithmeticCharts1359a
import SourceGammaOneSpecializationCharts1360a
import Dubon2026.SourceGammaOneResiduePlaceOrders

/-! DUB-17/18 -> original Gamma1 Picard inertia and Frobenius -> arithmetic
equivariance of specialization. The original and residue decomposition
actions transport the exact same integral chart condition. No place-map
equivariance is assumed; it follows from monic equations and literal residues. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => functionFieldOver Γ Qbar
local notation "Fb" => residueImage A Γ

theorem nonunit_decompositionResiduePlace_iff (d : A.decompositionSubgroup ℚ)
    (P : Place kk Fb) (f : Fb) :
    f ∈ (decompositionResiduePlace A Γ d P).toValuationSubring.nonunits ↔
      decompositionResidueAut A Γ d⁻¹ f ∈ P.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    mem_decompositionResiduePlace_iff, map_inv₀]
  simp only [map_eq_zero]

theorem decompositionResidueAut_j (d : A.decompositionSubgroup ℚ) :
    decompositionResidueAut A Γ d (residueJCoordinate A Γ) = residueJCoordinate A Γ := by
  let x : coefficientGaussRing Γ A :=
    ⟨jCoordinateOver Γ Qbar, jCoordinateOver_mem_gaussRing A Γ⟩
  have hx : decompositionGaussHom A Γ d x = x :=
    Subtype.ext (arithmeticRingAut_j Γ d.val)
  have hj : residueToImage A Γ x = residueJCoordinate A Γ :=
    regularProlongation_jCoordinateOver A Γ
  have h := decompositionGaussHom_residueToImage A Γ d x
  rw [hx, hj] at h
  exact h.symm

theorem decompositionResiduePlace_j_mem (d : A.decompositionSubgroup ℚ)
    (P : Place kk Fb) :
    residueJCoordinate A Γ ∈ (decompositionResiduePlace A Γ d P).toValuationSubring ↔
      residueJCoordinate A Γ ∈ P.toValuationSubring := by
  rw [mem_decompositionResiduePlace_iff, decompositionResidueAut_j]

theorem chartReducesTo_decomposition (d : A.decompositionSubgroup ℚ)
    (P : Place Qbar FF) (Q : Place kk Fb) (y : FF)
    (hy : arithmeticRingAut Γ d.val.symm y = y)
    (hP : ChartReducesTo A (regularProlongation A Γ) y P Q) :
    ChartReducesTo A (regularProlongation A Γ) y
      (arithmeticPlace Γ d.val P) (decompositionResiduePlace A Γ d Q) := by
  intro f hf a ha
  let f' := decompositionGaussHom A Γ d⁻¹ f
  have hf' : IsIntegral (Algebra.adjoin Qbar {y}) (f' : FF) :=
    arithmeticRingAut_isIntegral Γ d.val.symm y hy hf
  have ha' : (f' : FF) - algebraMap Qbar FF (d⁻¹ • a) ∈ P.toValuationSubring.nonunits := by
    have h := (nonunit_arithmeticPlace_iff Γ d.val P _).mp ha
    rw [map_sub, arithmeticRingAut_constants] at h
    exact h
  have h := hP f' hf' (d⁻¹ • a) ha'
  have hr := decompositionGaussHom_residueToImage A Γ d⁻¹ f
  change residueToImage A Γ f' = _ at hr
  change residueToImage A Γ f - algebraMap kk Fb (IsLocalRing.residue A a) ∈
    (decompositionResiduePlace A Γ d Q).toValuationSubring.nonunits
  rw [nonunit_decompositionResiduePlace_iff, map_sub,
    decompositionResidueAut_constants, ← hr, ← IsLocalRing.ResidueField.residue_smul]
  exact h

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
''')
out('SourceGammaOneConstantReductionCharts1362a.lean','''import SourceGammaOneSpecializationCharts1360a
import SourceGammaOnePicardTorsion

/-! DUB-17/18 -> original Gamma1 Picard inertia -> the same specialization
with its exact two chart descriptions and invertible-torsion injectivity.
All three properties belong to one constructed reduction. Coordinate-degree
and genus preservation remain explicit original geometric inputs. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation IntermediateField
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (M : ℕ) [NeZero M]
local notation "Δ" => CongruenceSubgroup.Gamma1 M
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => functionFieldOver Δ Qbar
local notation "Fb" => residueImage A Δ

theorem exists_gammaOne_constant_reduction_with_charts_of_degree_genus_eq
    (hdeg : Module.finrank Qbar⟮jCoordinateOver Δ Qbar⟯ FF =
      Module.finrank kk⟮residueJCoordinate A Δ⟯ Fb)
    (hgen : genusFF kk Fb = genusFF Qbar FF) :
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = regularProlongation A Δ ∧
      (∀ P Q, residueJCoordinate A Δ ∈ Q.toValuationSubring →
        (R.placeMap P = Q ↔ ChartDomain A P (jCoordinateOver Δ Qbar) ∧
          ChartReducesTo A R.toRegularProlongation (jCoordinateOver Δ Qbar) P Q)) ∧
      (∀ P Q, residueJCoordinate A Δ ∉ Q.toValuationSubring →
        (R.placeMap P = Q ↔ ChartDomain A P (jCoordinateOver Δ Qbar)⁻¹ ∧
          ChartReducesTo A R.toRegularProlongation (jCoordinateOver Δ Qbar)⁻¹ P Q)) ∧
      ∀ m : ℕ, (m : kk) ≠ 0 →
        Set.InjOn R.pic0Map (↑(Pic0.torsion (K := Qbar) (F := FF) m)) := by
  have hT : ModularGroup.T ∈ Δ := by simp [CongruenceSubgroup.Gamma1_mem, ModularGroup.T]
  haveI := finiteDimensional_jCoordinateOver hT Qbar
  obtain ⟨r, hr₁, hr₂, hr⟩ :=
    exists_principal_reduction_map_with_charts_of_degree_genus_eq A Δ hT hdeg hgen
  let R : ConstantReduction A FF Fb := ConstantReduction.ofPlaceMap
    (regularProlongation A Δ) r
    (place_residue_bijective_of_finite_coordinate (jCoordinateOver Δ Qbar))
    (residueImage_place_residue_bijective A Δ hT) hr
  refine ⟨R, rfl, hr₁, hr₂, fun m hm x hx y hy hxy => ?_⟩
  apply sub_eq_zero.mp
  apply gammaOne_pic0_eq_zero_of_torsion_of_degree_genus_eq A M hdeg hgen R rfl m hm (x - y)
  · rw [nsmul_sub, Pic0.mem_torsion_iff.mp hx, Pic0.mem_torsion_iff.mp hy, sub_self]
  · rw [map_sub, hxy, sub_self]

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
''')
out('SourceGammaOneSpecializationEquivariance1363a.lean','''import SourceGammaOneDecompositionCharts1361a
import SourceGammaOneConstantReductionCharts1362a

/-! DUB-17/18 -> original Gamma1 Tate Frobenius/inertia -> arithmetic
equivariance of actual specialization places. Transport the proved exact
chart descriptions under the original and residue coefficient actions.
The same reduction retains its injectivity on every invertible torsion group;
only coordinate-degree and genus preservation remain geometric premises. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation IntermediateField
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (M : ℕ) [NeZero M]
local notation "Δ" => CongruenceSubgroup.Gamma1 M
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => functionFieldOver Δ Qbar
local notation "Fb" => residueImage A Δ

theorem exists_gammaOne_reduction_decomposition_equivariant_of_degree_genus_eq
    (hdeg : Module.finrank Qbar⟮jCoordinateOver Δ Qbar⟯ FF =
      Module.finrank kk⟮residueJCoordinate A Δ⟯ Fb)
    (hgen : genusFF kk Fb = genusFF Qbar FF) :
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = regularProlongation A Δ ∧
      (∀ m : ℕ, (m : kk) ≠ 0 →
        Set.InjOn R.pic0Map (↑(Pic0.torsion (K := Qbar) (F := FF) m))) ∧
      ∀ (d : A.decompositionSubgroup ℚ) (P : Place Qbar FF),
        R.placeMap (arithmeticPlace Δ d.val P) = decompositionResiduePlace A Δ d (R.placeMap P) := by
  obtain ⟨R, hR, h₁, h₂, hinj⟩ :=
    exists_gammaOne_constant_reduction_with_charts_of_degree_genus_eq A M hdeg hgen
  refine ⟨R, hR, hinj, ?_⟩
  intro d P
  let Q := R.placeMap P
  let Q' := decompositionResiduePlace A Δ d Q
  have htransport (y : FF) (hy : arithmeticRingAut Δ d.val.symm y = y)
      (h : ChartDomain A P y ∧ ChartReducesTo A R.toRegularProlongation y P Q) :
      ChartDomain A (arithmeticPlace Δ d.val P) y ∧
        ChartReducesTo A R.toRegularProlongation y (arithmeticPlace Δ d.val P) Q' := by
    refine ⟨chartDomain_arithmeticPlace Δ A d P y hy h.1, ?_⟩
    rw [hR] at h ⊢
    exact chartReducesTo_decomposition A Δ d P Q y hy h.2
  have hQiff : residueJCoordinate A Δ ∈ Q'.toValuationSubring ↔
      residueJCoordinate A Δ ∈ Q.toValuationSubring := decompositionResiduePlace_j_mem A Δ d Q
  by_cases hQ : residueJCoordinate A Δ ∈ Q.toValuationSubring
  · exact (h₁ _ Q' (hQiff.mpr hQ)).mpr
      (htransport _ (arithmeticRingAut_j Δ d.val.symm) ((h₁ P Q hQ).mp rfl))
  · apply (h₂ _ Q' (fun h => hQ (hQiff.mp h))).mpr
    apply htransport _ _ ((h₂ P Q hQ).mp rfl)
    rw [map_inv₀, arithmeticRingAut_j]

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
''')
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceGammaOneDecompositionCharts1361a','SourceGammaOneConstantReductionCharts1362a','SourceGammaOneSpecializationEquivariance1363a')")
out('build_gamma_one_chart_transport_1361.ps1',s)
print('Prepared exact arithmetic chart and specialization equivariance consumers.')
