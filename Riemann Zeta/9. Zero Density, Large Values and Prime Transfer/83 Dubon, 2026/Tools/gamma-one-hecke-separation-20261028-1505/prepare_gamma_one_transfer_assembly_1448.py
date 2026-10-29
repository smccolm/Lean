from pathlib import Path
s=Path(__file__).parent
c=(s/'SourceGammaOneDiamondQuotientHecke1440j.lean').read_text(encoding='utf-8')
vs=c[c.index('variable (Q p n w'):c.index('theorem gammaOne_diamond_relations_hecke')]
start=c.index('theorem exists_gammaOne_diamond_quotient_hecke')
a=c.index('    (ell :',start);b=c.index(' := by',a)
decl=c[a:b]
decl=decl.replace('(ell.val : ZMod N) ^ (w + 1) • 1','''(ell.val : ZMod N) ^ (w + 1) • 1 ∧
      (binaryDiamondQuotientOriginalTransfer Q p n w hlarge).comp Hq =
        (sourceBinaryH1PrimeOperators (ZMod N) Q w (sourceGammaOneHeckePrimeForget Q N ell)).comp
          (binaryDiamondQuotientOriginalTransfer Q p n w hlarge)''')
code='''import SourceGammaOneDiamondQuotientHecke1440j
import SourceGammaOneDiamondQuotientTransfer1444b

/-! DUB-17/18 -> original all-weight association -> finite original
Hecke-character realization. The actual descended Hecke operator from
the original geometric Frobenius theorem intertwines the original
cohomology transfer. Its operator, quotient polynomial and original
transfer square are derived together from degree/genus preservation;
no Hecke descent or transfer compatibility is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve CongruenceSubgroup IntermediateField

'''+vs+'''theorem exists_gammaOne_diamond_quotient_original_transfer_frobenius
    (hlarge : 3 < p)
'''+decl+''' := by
  have hs := exists_gammaOne_diamond_quotient_hecke_frobenius_of_degree_genus_eq Q p n w A ell
  have h1 := hs hdeg
  have h2 := h1 hgen
  have h3 := h2 d hd hp
  obtain ⟨Hq, hcomp, hpoly⟩ := h3
  refine ⟨Hq, hcomp, hpoly, ?_⟩
  exact binaryDiamondQuotientOriginalTransfer_hecke_of_intertwining Q p n w hlarge ell Hq hcomp

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
'''
t=s/'SourceGammaOneDiamondQuotientAssembly1448a.lean';assert not t.exists();t.write_text(code,encoding='utf-8')
print('Prepared the actual geometric-operator/original-transfer assembled consumer.')
