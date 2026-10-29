from pathlib import Path
import hashlib, json
s=Path(__file__).parent
p=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
src=p/'Extension'/'Dubon2026'
def write(name,code):
    t=s/name
    assert not t.exists(), t
    t.write_text(code,encoding='utf-8')
files=['SourceTateDualArithmeticQuadratic','SourceGammaOneArithmeticFrobenius','SourceGammaOneGeometricArithmeticFrobenius']
route={'scope':'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight association -> finite Hecke-character realization -> diamond-one quotient of the actual homogeneous Tate dual',
 'obligation':'Derive the operator-valued Frobenius polynomial before imposing diamond fixedness; use it on the actual quotient by diamond-minus-one relations, with Galois stability derived from the existing commutation theorem.',
 'reuse':'Existing fixed-class proof performs the same calculation but substitutes diamond fixedness. Retain that term. Reuse the original geometric Tate identity and actual cyclotomic Frobenius value. Native search found no existing diamond coinvariant construction. Mathlib Submodule quotient/span APIs avoid a new group-action construction; Representation.Coinvariants would additionally require packaging a diamond representation.',
 'limits':'Does not prove degree/genus preservation, nonzero Hecke-character realization, parabolic transfer, two-dimensionality or any acceptance gate.',
 'sources':{f:hashlib.sha256((src/(f+'.lean')).read_bytes()).hexdigest() for f in files}}
write('gamma-one-diamond-polynomial-route-1433.json',json.dumps(route,indent=2)+'\n')
c=(src/'SourceTateDualArithmeticQuadratic.lean').read_text(encoding='utf-8')
c=c.replace('theorem sourceTateDual_arithmetic_quadratic','theorem sourceTateDual_arithmetic_diamond_quadratic')
c=c.replace('(φ : T →ₗ[R] V) (hfixed : (c.restrictScalars R).comp (φ.comp D) = φ) :','(φ : T →ₗ[R] V) :')
c=c.replace('(ell : S) ^ (w + 1) • φ := by','(ell : S) ^ (w + 1) • (c.restrictScalars R).comp (φ.comp D) := by')
c=c.replace('(ell : S) ^ (w + 1) • φ x','(ell : S) ^ (w + 1) • c (φ (D x))')
c=c.replace('  have hf : c (φ (D x)) = φ x := LinearMap.congr_fun hfixed x\n','').replace('hc, hf, smul_smul','hc, smul_smul')
a=c.index('/-!');b=c.index('namespace',a)
c=c[:a]+'''/-! DUB-17/18 -> original all-weight association -> finite Hecke-character
quotient. Retain the combined diamond in the inverse-action Frobenius
identity, so that it can descend through actual diamond-minus-one
relations. No fixed-vector hypothesis is imposed. -/
'''+c[b:]
write('SourceTateDualArithmeticDiamond1433a.lean',c)
c=(src/'SourceGammaOneArithmeticFrobenius.lean').read_text(encoding='utf-8')
c=c.replace('import Dubon2026.SourceTateDualArithmeticQuadratic','import SourceTateDualArithmeticDiamond1433a\nimport Dubon2026.SourceGammaOneArithmeticFrobenius')
a=c.index('/-- Inverse arithmetic');b=c.index('theorem ',a);c=c[:a]+c[b:]
c=c.replace('binaryTateArithmeticFrobeniusOperator_quadratic_of_picard','binaryTateArithmeticFrobeniusOperator_diamond_quadratic_of_picard')
c=c.replace('    (φ : T →ₗ[ℤ_[p]] V)\n    (hfixed : ((sourceGammaOneBinaryDiamondCoefficient Q N w g).restrictScalars ℤ_[p]).comp\n      (φ.comp (arithmeticDiamondTate M p g)) = φ) :','    (φ : T →ₗ[ℤ_[p]] V) :')
c=c.replace('(ell.val : ZMod N) ^ (w + 1) • φ := by','(ell.val : ZMod N) ^ (w + 1) •\n        ((sourceGammaOneBinaryDiamondCoefficient Q N w g).restrictScalars ℤ_[p]).comp\n          (φ.comp (arithmeticDiamondTate M p g)) := by')
c=c.replace('sourceTateDual_arithmetic_quadratic','sourceTateDual_arithmetic_diamond_quadratic').replace(' φ hfixed',' φ')
a=c.index('/-!');b=c.index('namespace',a)
c=c[:a]+'''/-! DUB-17/18 -> original all-weight association -> finite Hecke-character
quotient. The actual original coefficient matrices and inverse Picard
action give the Frobenius polynomial with its combined diamond term on
every homogeneous-valued Tate class. -/
'''+c[b:]
write('SourceGammaOneArithmeticDiamond1434a.lean',c)
c=(src/'SourceGammaOneGeometricArithmeticFrobenius.lean').read_text(encoding='utf-8')
c=c.replace('import Dubon2026.SourceGammaOneArithmeticFrobenius','import SourceGammaOneArithmeticDiamond1434a')
c=c.replace('exists_gammaOne_arithmetic_frobenius_quadratic_of_degree_genus_eq','exists_gammaOne_arithmetic_frobenius_diamond_quadratic_of_degree_genus_eq')
c=c.replace('        ((sourceGammaOneBinaryDiamondCoefficient Q N w g).restrictScalars ℤ_[p]).comp\n          (φ.comp (arithmeticDiamondTate M p g)) = φ →\n','')
c=c.replace('(ell.val : ZMod N) ^ (w + 1) • φ := by','(ell.val : ZMod N) ^ (w + 1) •\n              ((sourceGammaOneBinaryDiamondCoefficient Q N w g).restrictScalars ℤ_[p]).comp\n                (φ.comp (arithmeticDiamondTate M p g)) := by')
c=c.replace('fun φ hφ =>','fun φ =>').replace('binaryTateArithmeticFrobeniusOperator_quadratic_of_picard','binaryTateArithmeticFrobeniusOperator_diamond_quadratic_of_picard').replace(' hquad φ hφ',' hquad φ')
a=c.index('/-!');b=c.index('namespace',a)
c=c[:a]+'''/-! DUB-17/18 -> original all-weight association -> finite Hecke-character
quotient. Consume the original norm-derived Picard/Tate relation to
derive the diamond-valued Frobenius polynomial on every Tate class.
Coordinate-degree and genus preservation remain explicit geometric inputs;
neither the polynomial nor diamond fixedness is assumed. -/
'''+c[b:]
write('SourceGammaOneGeometricDiamond1435a.lean',c)
runner='''$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\\Users\\Naraphim\\.elan'
$env:LEAN_PATH='E:\\Lean\\.tmp\\dubon83'
Set-Location -LiteralPath 'E:\\Lean\\Riemann Zeta\\9. Zero Density, Large Values and Prime Transfer\\83 Dubon, 2026\\Extension'
$names=@('SourceTateDualArithmeticDiamond1433a','SourceGammaOneArithmeticDiamond1434a','SourceGammaOneGeometricDiamond1435a')
foreach($n in $names){
 $base="E:\\Lean\\.tmp\\dubon83\\$n"
 if(Test-Path -LiteralPath "$base.log"){throw "Evidence exists: $base"}
 & 'C:\\Users\\Naraphim\\.elan\\bin\\lake.exe' env lean -DautoImplicit=false -R 'E:\\Lean\\.tmp\\dubon83' -o "$base.olean" "$base.lean" *> "$base.log"
 $rc=$LASTEXITCODE
 $rc | Out-File -LiteralPath "$base.exit" -Encoding ascii
 if($rc -ne 0 -or (Get-Item -LiteralPath "$base.log").Length -ne 0){Get-Content -LiteralPath "$base.log" -Encoding Unicode;exit 1}
 Write-Output "PASS: $n"
}
'''
write('build_gamma_one_diamond_polynomial_1433.ps1',runner)
print('Prepared three fresh scratch consumers and route review.')
