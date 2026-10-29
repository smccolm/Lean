from pathlib import Path
s=Path(__file__).parent
def write(name,code):
 t=s/name;assert not t.exists(),t;t.write_text(code,encoding='utf-8')
c=(s/'SourceGammaOneTwistedGaloisFrobenius1406d.lean').read_text(encoding='utf-8')
c=c.replace('import SourceGammaOneGeometricArithmeticFrobenius','import SourceGammaOneGeometricDiamond1435a')
c=c.replace('(a : R) (x : W) (he : F = G)','(a : R) (x y : W) (he : F = G)')
c=c.replace('+ a • x', '+ a • y')
c=c.replace('exists_gammaOne_galois_frobenius_quadratic_of_degree_genus_eq','exists_gammaOne_galois_frobenius_diamond_quadratic_of_degree_genus_eq')
c=c.replace('        ((sourceGammaOneBinaryDiamondCoefficient Q N w g).restrictScalars ℤ_[p]).comp\n          (φ.comp (arithmeticDiamondTate M p g)) = φ →\n','')
c=c.replace('(ell.val : ZMod N) ^ (w + 1) • φ := by','(ell.val : ZMod N) ^ (w + 1) •\n              ((sourceGammaOneBinaryDiamondCoefficient Q N w g).restrictScalars ℤ_[p]).comp\n                (φ.comp (arithmeticDiamondTate M p g)) := by')
c=c.replace('exists_gammaOne_arithmetic_frobenius_quadratic_of_degree_genus_eq','exists_gammaOne_arithmetic_frobenius_diamond_quadratic_of_degree_genus_eq')
c=c.replace('fun φ hφ =>','fun φ =>')
c=c.replace('φ he (hq φ hφ)','φ\n      (((sourceGammaOneBinaryDiamondCoefficient Q N w g).restrictScalars ℤ_[p]).comp\n        (φ.comp (arithmeticDiamondTate M p g))) he (hq φ)')
a=c.index('/-!');b=c.index('namespace',a)
c=c[:a]+'''/-! DUB-17/18 -> original all-weight association -> finite Hecke-character
quotient. The actual cyclotomic value and norm-derived geometric identity
give the global Galois Frobenius polynomial, retaining its combined diamond
operator on every class. Only coordinate-degree/genus preservation remain. -/
'''+c[b:]
write('SourceGammaOneGaloisDiamondPolynomial1436a.lean',c)
write('run_scratch_module_1433.ps1',r'''param([Parameter(Mandatory=$true)][string]$Name)
$ErrorActionPreference='Stop'
if($Name -notmatch '^[A-Za-z0-9_]+$'){throw 'Invalid scratch module name'}
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$base="E:\Lean\.tmp\dubon83\$Name"
if(Test-Path -LiteralPath "$base.log"){throw "Evidence exists: $base"}
& 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false -R 'E:\Lean\.tmp\dubon83' -o "$base.olean" "$base.lean" *> "$base.log"
$rc=$LASTEXITCODE
$rc | Out-File -LiteralPath "$base.exit" -Encoding ascii
if($rc -ne 0 -or (Get-Item -LiteralPath "$base.log").Length -ne 0){Get-Content -LiteralPath "$base.log" -Encoding Unicode;exit 1}
Write-Output "PASS: $Name"
''')
print('Prepared global diamond polynomial and fresh-evidence runner.')
