from pathlib import Path
s=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026\SourceLaurentDegreeTransportIndependence.lean').read_text(encoding='utf-8')
a=src[src.index('theorem linearIndependent_pow_mul'):src.index('theorem exists_common_denom')]
a=a.replace(' (ht : t ∈ F₀)','').replace('ℚ','K').replace('E₀ F₀ t ht','LaurentSeries K').replace('K₀ t','K⟮t⟯')
a=a.replace('    apply Subtype.ext\n    rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]\n','')
b=src[src.index('theorem exists_common_denom'):src.index('theorem linearIndependent_ψ')]
b=b.replace('theorem exists_common_denom','theorem exists_common_denom (j : LaurentSeries L)').replace('K L t','L⟮j⟯').replace('coeffEmb L t','j')
head='''import SourceReducedBaseCoordinateMap1702b
import Dubon2026.SourceLaurentScalarIndependence

/-! DUB-17/18 -> original Gamma1 degree preservation -> signed-index bound
-> finite coordinate degree transport from the actual residue field.
Reuse the native rational-coordinate independence proof over the coefficient
field needed here. Transcendence makes the coordinate powers independent;
finite polynomial denominator clearing prepares the coefficient extension.
Only the finite-family direction needed for the degree inequality is selected.
The original source is the pinned Apache-2.0 FLT solution at
6e837e75355538c7f80bab5b956861e86c4eacc2; the existing native proof supplies
the shorter route and no external proof options are adopted. -/
namespace Dubon2026.SourceFunctionField.ReducedDegreeTransport
noncomputable section
open IntermediateField Polynomial
open scoped IntermediateField
variable {K L : Type*} [Field K] [Field L] {t : LaurentSeries K}

'''
f=s/'SourceReducedCoordinateIndependence1707a.lean';assert not f.exists()
f.write_text(head+a+b+'end\nend Dubon2026.SourceFunctionField.ReducedDegreeTransport\n',encoding='utf-8')
print('Prepared native finite-coordinate independence adaptation.')
