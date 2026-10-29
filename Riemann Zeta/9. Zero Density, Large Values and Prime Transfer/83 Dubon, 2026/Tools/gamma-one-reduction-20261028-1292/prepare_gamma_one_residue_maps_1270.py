from pathlib import Path
import re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
jobs=[('SourceModularGaussResidueHom','SourceGammaOneGaussResidueHom','SourceGammaOneGaussValuation','1270a'),
 ('SourceModularGaussResidueKernel','SourceGammaOneGaussResidueKernel','SourceGammaOneGaussResidueHom','1271a'),
 ('SourceModularGaussConstants','SourceGammaOneGaussConstants','SourceGammaOneGaussResidueKernel','1272a')]
for old,new,dep,attempt in jobs:
 s=(r/(old+'.lean')).read_text(encoding='utf-8')
 s=re.sub(r'^import [^\n]+','import '+dep,s,count=1)
 a=s.index('/-!');b=s.index('-/',a)+2
 s=s[:a]+'''/-! DUB-17/18 -> original Gamma1 Tate Frobenius/inertia -> original
good reduction -> literal coefficient reduction. Reuse the original
integral-fraction residue proof on the actual Gamma1 scalar-extended field.
The residue formula is independent of its integral fraction witness.
These maps and kernel/constant identities do not assert genus preservation
or good reduction; those remain subsequent mathematical obligations. -/'''+s[b:]
 s=s.replace('Dubon2026.SourceFunctionField.GaussReduction',
 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction')
 s=s.replace('open Polynomial IntermediateField','open Polynomial IntermediateField GaussReduction')
 s=s.replace('variable {L : Type*} [Field L] (A : ValuationSubring L) (N : ℕ)',
 'variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)\n  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))')
 s=s.replace('modularFunctionFieldCoeff N L','functionFieldOver Γ L')
 s=s.replace('mem_gaussRing_iff A N','mem_coefficientGaussRing_iff Γ A')
 s=s.replace('gaussRing A N','coefficientGaussRing Γ A')
 s=re.sub(r'\bN\b','Γ',s)
 if old=='SourceModularGaussConstants':
  oldline='  obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, _, _, h⟩ := exists_frac_form A Γ f hf'
  assert oldline in s
  s=s.replace(oldline,'''  have hx : (f : LaurentSeries L) ∈ qExpFunctionFieldC L Γ := by
    rw [← functionFieldOver_eq_qExpFunctionFieldC Γ L]
    exact f.property
  have hx0 : (f : LaurentSeries L) ≠ 0 := fun h => hf (Subtype.ext h)
  obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, h⟩ :=
    qExpFunctionField_exists_primitive_fraction A Γ hx hx0''')
 out=p/(new+'.lean');assert not out.exists();out.write_text(s,encoding='utf-8')
 t=(p/'compile_gamma_one_gauss_criterion_1268a.ps1').read_text(encoding='utf-8')
 out=p/('compile_'+new+'_'+attempt+'.ps1');assert not out.exists()
 out.write_text(t.replace('SourceGammaOneGaussCriterion',new).replace('1268a',attempt),encoding='utf-8')
 print(new)
