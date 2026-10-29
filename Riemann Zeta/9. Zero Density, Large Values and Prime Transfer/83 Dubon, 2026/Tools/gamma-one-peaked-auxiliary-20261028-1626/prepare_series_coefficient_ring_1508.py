from pathlib import Path
s=Path(__file__).parent
f=s/'anthropic-series-coefficient-depth-1507/S_PowerSeries_coeff_mem_subring_of_coeff_mul_mem.lean.txt'
t=f.read_text(encoding='utf-8');t=t[t.index('theorem solution'):]
t=t.replace('theorem solution {K : Type*} [CommRing K] (R : Subring K)', 'theorem coeff_mem_of_product_initial_coeff_mem (R : Subring ℂ)').replace('(P U : PowerSeries K)', '(P U : PowerSeries ℂ)')
head='''import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. Recover precisely the needed
coefficient of the original series from finitely many coefficients of its
product with the auxiliary series. The leading auxiliary coefficient has
its inverse in the prescribed subring; no coefficient of the target is
assumed directly. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_PowerSeries_coeff_mem_subring_of_coeff_mul_mem.lean. -/
namespace Dubon2026.SourceFunctionField.LevelOneCoefficientRing

'''
out=s/'SourceTraceProductCoefficientRing1508a.lean';assert not out.exists()
out.write_text(head+t+'\nend Dubon2026.SourceFunctionField.LevelOneCoefficientRing\n',encoding='utf-8')
