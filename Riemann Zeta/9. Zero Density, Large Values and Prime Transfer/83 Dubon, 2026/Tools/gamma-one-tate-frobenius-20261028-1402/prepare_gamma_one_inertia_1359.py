from pathlib import Path
import json,hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
def out(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
native=['SourceOriginalArithmeticIntegralCharts','SourceOriginalInertiaChartTransport','SourceDecompositionChartTransport','SourceReductionPrincipalDivisorCharts','SourceGammaOneArithmeticPlaces','SourceGammaOneArithmeticPicard','SourceGammaOneResidueArithmetic','SourceGammaOneResiduePlaces','SourceGammaOneResiduePlaceOrders','SourceModularDecompositionPlaceReduction']
out('gamma-one-inertia-route-1359.json',json.dumps(dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> original all-weight arithmetic association -> original Picard/H1/Tate realization -> original Gamma1 inertia on invertible Picard torsion.',reuse=[dict(path=str(r/(n+'.lean')),sha256=sha(r/(n+'.lean'))) for n in native],selected='Reuse native exact two-chart gluing, monic-equation transport, original arithmetic place and Picard actions, actual residue decomposition action and the newly proved Picard torsion kernel theorem. Retain the chart specification of the already constructed specialization; derive its arithmetic equivariance and inertia triviality without a new curve or valuation framework.',discharge='Actual specialization-place inertia invariance, then inertia invariance of original Picard torsion and the corresponding Tate system.',remaining='Original coordinate-degree equality and genus preservation remain explicit. Hecke norm/place/Picard compatibility, geometric Frobenius relation, parabolic and coefficient realization, all-weight association and literal higher continuation remain. 16/20; DUB-17--20 OPEN.',productionMutation=False),indent=2)+'\n')
out('SourceGammaOneArithmeticCharts1359a.lean','''import Dubon2026.SourceGammaOneArithmeticPlaces
import Dubon2026.SourceReductionChartGluing
import Dubon2026.SourceGammaOneDecompositionGauss

/-! DUB-17/18 -> original Gamma1 Tate inertia -> arithmetic compatibility
of actual place specialization. Transport the native monic chart equations
and valuation nonunits by the original coefficient automorphism. These are
the exact two charts used by the existing specialization construction. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
local notation "Qbar" => AlgebraicClosure ℚ
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
local notation "F" => functionFieldOver Γ Qbar

theorem arithmeticRingAut_mem_adjoin (σ : Qbar ≃ₐ[ℚ] Qbar)
    (y : F) (hy : arithmeticRingAut Γ σ y = y)
    {f : F} (hf : f ∈ Algebra.adjoin Qbar ({y} : Set F)) :
    arithmeticRingAut Γ σ f ∈ Algebra.adjoin Qbar ({y} : Set F) := by
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl := Set.mem_singleton_iff.mp hx
    rw [hy]
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  | algebraMap a =>
    rw [arithmeticRingAut_constants]
    exact (Algebra.adjoin Qbar ({y} : Set F)).algebraMap_mem _
  | add x z _ _ hx hz => simpa only [map_add] using add_mem hx hz
  | mul x z _ _ hx hz => simpa only [map_mul] using mul_mem hx hz

theorem arithmeticRingAut_isIntegral (σ : Qbar ≃ₐ[ℚ] Qbar)
    (y : F) (hy : arithmeticRingAut Γ σ y = y)
    {f : F} (hf : IsIntegral (Algebra.adjoin Qbar ({y} : Set F)) f) :
    IsIntegral (Algebra.adjoin Qbar ({y} : Set F)) (arithmeticRingAut Γ σ f) := by
  let φ : Algebra.adjoin Qbar ({y} : Set F) →+* Algebra.adjoin Qbar ({y} : Set F) :=
    { toFun := fun f => ⟨arithmeticRingAut Γ σ f.val,
        arithmeticRingAut_mem_adjoin Γ σ y hy f.property⟩
      map_one' := Subtype.ext (map_one (arithmeticRingAut Γ σ))
      map_mul' := fun f g => Subtype.ext (map_mul (arithmeticRingAut Γ σ) f.val g.val)
      map_zero' := Subtype.ext (map_zero (arithmeticRingAut Γ σ))
      map_add' := fun f g => Subtype.ext (map_add (arithmeticRingAut Γ σ) f.val g.val) }
  exact IsIntegral.map_of_comp_eq φ (arithmeticRingAut Γ σ).toRingHom (by ext x; rfl) hf

theorem nonunit_arithmeticPlace_iff (σ : Qbar ≃ₐ[ℚ] Qbar)
    (P : Place Qbar F) (f : F) :
    f ∈ (arithmeticPlace Γ σ P).toValuationSubring.nonunits ↔
      arithmeticRingAut Γ σ.symm f ∈ P.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  change f = 0 ∨ arithmeticRingAut Γ σ.symm f⁻¹ ∉ P.toValuationSubring ↔ _
  rw [map_inv₀]
  simp only [map_eq_zero]

theorem chartDomain_arithmeticPlace (A : ValuationSubring Qbar)
    (d : A.decompositionSubgroup ℚ) (P : Place Qbar F) (y : F)
    (hy : arithmeticRingAut Γ d.val.symm y = y) (hP : ChartDomain A P y) :
    ChartDomain A (arithmeticPlace Γ d.val P) y := by
  obtain ⟨a, ha⟩ := hP
  refine ⟨d • a, (nonunit_arithmeticPlace_iff Γ d.val P _).mpr ?_⟩
  rw [map_sub, hy, arithmeticRingAut_constants]
  change y - algebraMap Qbar F (d.val.symm (d.val a)) ∈ P.toValuationSubring.nonunits
  simpa only [AlgEquiv.symm_apply_symm_apply, AlgEquiv.symm_apply_apply] using ha

end
end Dubon2026.SourceFunctionField.GammaOne
'''.replace('AlgEquiv.symm_apply_symm_apply, ',''))
s=(p/'SourceGammaOneGenusSpecialization.lean').read_text(encoding='utf-8')
a=s.index('theorem exists_principal_reduction_map_of_degree_genus_eq')
b=s.index('\ntheorem exists_constant_reduction_of_degree_genus_eq')
body=s[a:b].replace('exists_principal_reduction_map_of_degree_genus_eq','exists_principal_reduction_map_with_charts_of_degree_genus_eq')
body=body.replace('    ∃ r : Place Qbar FF → Place kk Fb,\n','''    ∃ r : Place Qbar FF → Place kk Fb,
      (∀ P Q, residueJCoordinate A Γ ∈ Q.toValuationSubring →
        (r P = Q ↔ ChartDomain A P (jCoordinateOver Γ Qbar) ∧
          ChartReducesTo A (regularProlongation A Γ) (jCoordinateOver Γ Qbar) P Q)) ∧
      (∀ P Q, residueJCoordinate A Γ ∉ Q.toValuationSubring →
        (r P = Q ↔ ChartDomain A P (jCoordinateOver Γ Qbar)⁻¹ ∧
          ChartReducesTo A (regularProlongation A Γ) (jCoordinateOver Γ Qbar)⁻¹ P Q)) ∧
''')
body=body.replace('  exact @exists_principal_divisor_reduction_map\n','  have hc := @exists_principal_divisor_reduction_map_with_charts\n')
body += '  simpa only [hres] using hc\n'
out('SourceGammaOneSpecializationCharts1360a.lean','''import SourceGammaOneGenusSpecialization
import Dubon2026.SourceReductionPrincipalDivisorCharts

/-! DUB-17/18 -> original Gamma1 Picard inertia -> exact specialization
charts. Retain the two chart descriptions from the existing native gluing
theorem. Coordinate-degree and actual adelic-genus equality remain explicit;
the new information is the chart specification needed for arithmetic transport. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve SourceCurve.RegularProlongation
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
  (hT : ModularGroup.T ∈ Γ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => functionFieldOver Γ Qbar
local notation "Fb" => residueImage A Γ

include hT

'''+body+'\nend\nend Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction\n')
out('build_gamma_one_inertia_1359.ps1',r'''$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH=$taskScratch
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
foreach($taskName in @('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')){
 $taskBase=Join-Path $taskScratch $taskName
 if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence already exists'}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false -R $taskScratch -o "$taskBase.olean" "$taskBase.lean" *> "$taskBase.log"
 $taskCode=$LASTEXITCODE
 $taskCode | Set-Content -LiteralPath "$taskBase.exit"
 if($taskCode -ne 0){Get-Content -LiteralPath "$taskBase.log";exit $taskCode}
 if((Get-Item -LiteralPath "$taskBase.log").Length -ne 0){Get-Content -LiteralPath "$taskBase.log";exit 1}
 Write-Output "PASS $taskName"
}
''')
print('Prepared arithmetic chart transport and exact specialization charts; no production changes.')
