from pathlib import Path
import hashlib,json
s=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
fs=[src/(n+'.lean') for n in ['SourceGammaOneDiamondTransfer','SourceGammaOneTransferHecke','SourceGammaOneBinaryDiamondTateH1','SourceGammaOneBinaryTateHecke','SourceGammaOneParabolicTransferCriterion','SourceGammaOneParabolicCharacterTransfer']]
fs.append(s/'SourceGammaOneTateDiamondRelations1437e.lean')
r=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> automorphy -> original all-weight association -> actual finite Hecke-character realization -> original transfer through the diamond quotient',reuse=[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper()) for f in fs],selected='Compose the proved original Tate/H1 and native cohomology transfer maps. Reuse the exact original diamond invariance and Hecke correspondence identity. This will descend through diamond-minus-one relations, retaining the actual original operator and character kernel. No new group-cohomology transfer is constructed.',remaining='The original parabolic preimage property remains unproved. Full H1 surjectivity is not used as parabolic surjectivity. The existing comparison retains 3<p. Geometric degree/genus equality, nonzero two-dimensional original character realization and full acceptance gates remain open.',proofLimitsChanged=False)
t=s/'gamma-one-tate-transfer-route-1443.json';assert not t.exists();t.write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
print('Recorded native transfer reuse before compiling the composed consumer.')
