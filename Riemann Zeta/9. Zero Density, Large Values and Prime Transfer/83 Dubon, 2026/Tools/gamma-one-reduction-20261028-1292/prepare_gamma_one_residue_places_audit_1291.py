from pathlib import Path
import ast
p=Path(__file__).parent
s=(p/'prepare_gamma_one_residue_frobenius_audit_1287.py').read_text(encoding='utf-8')
s=s.replace("mods=['SourceGammaOneResidueFrobenius']", "mods=['SourceGammaOneResiduePlaces','SourceGammaOneResiduePlaceOrders','SourceGammaOneResidueFrobeniusPlaces']\nev=dict(zip(mods,['1288a','1289a','1290a'],strict=True))")
s=s.replace("m+'1286d.exit'", "m+ev[m]+'.exit'").replace("m+'1286d.log'", "m+ev[m]+'.log'")
a=s.index('roots=[cn+x');b=s.index('prev=json.loads',a)
s=s[:a]+'''roots=[cn+x for x in ['decompositionResiduePlaceEquiv',
 'decompositionResiduePlace_ord_action','decompositionResiduePlace_eq_self_of_inertia',
 'geometricFrobenius_place_order']]
edges=[x for x in ths+defs if not x.endswith('.mem_decompositionResiduePlace_iff')]+[
 cn+'decompositionResidueAut',cn+'decompositionResidueAut_eq_one_of_inertia',
 cn+'geometricFrobenius','Dubon2026.SourceCurve.Place.eq_ord_of_addHom_of_nonneg_iff',
 'Dubon2026.SourceCurve.Place.ord_zpow']
'''+s[b:]
s=s.replace("source-gamma-one-residue-compatibility-1-audit-config.json", "source-gamma-one-residue-frobenius-1-audit-config.json")
s=s.replace("compileEvidence={m:m+'1286d' for m in mods}", "compileEvidence={m:m+ev[m] for m in mods}")
s=s.replace('(8,1,16)','(10,4,18)')
s=s.replace("stem='source-gamma-one-residue-frobenius-1'", "stem='source-gamma-one-residue-places-1'")
s=s.replace("new='SourceGammaOneResidueFrobenius'", "new='SourceGammaOneResiduePlaces'")
s=s.replace("'ScratchOwnership1287'", "'ScratchOwnership1291'")
s=s.replace('GAMMA ONE RESIDUE FROBENIUS','GAMMA ONE RESIDUE PLACES')
s=s.replace('actual Gamma1 residue geometric Frobenius integrality, finiteness and original Hecke beta factorization', 'actual Gamma1 residue decomposition permutation, inertia identity and geometric Frobenius place restriction with normalized order multiplied by p')
a=s.index("reuse=[r/'Extension");b=s.index('route=dict(',a)
s=s[:a]+'''reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in [
 'SourceCurvePlaceTransport','SourceResidueCoefficientPlaces',
 'SourceResidueCoefficientPlaceOrders','SourceResidueGeometricFrobeniusPlaces']]
reuse += [p/'source-gamma-one-residue-compatibility-1-scratch-receipt.json',
 p/'source-gamma-one-residue-frobenius-1-scratch-receipt.json']
'''+s[b:]
a=s.index(' chain=');b=s.index(' externalBuild=',a)
s=s[:a]+''' chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 Picard/Tate Frobenius and inertia -> equivariant specialization on places -> actual decomposition and geometric Frobenius on residue places.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='Reuse the existing normalized discrete-order uniqueness and the native coefficient-place construction, specialized to the already constructed actual Gamma1 residue image. Literal valuation-ring transport proves discreteness. The actual coefficient automorphism supplies the inverse permutation and inertia identity. Comap along geometric Frobenius equals that coefficient place, so discreteness and the exact order multiplier p follow directly without adding a separate degree argument or generic scheme framework.',
 assumptionsToDischarge=[
 'The actual decomposition action permutes all genuine places of the original Gamma1 residue field and preserves normalized orders with the precise inverse convention.',
 'Original arithmetic inertia fixes the actual residue places.',
 'For an actual decomposition element with pth-power action on residue constants, restriction along the original geometric Frobenius is exactly that decomposition permutation, with normalized orders multiplied by p.'],
 remaining='The arithmetic Frobenius constant-action premise is explicit. The original norm identity, degree equality, genus preservation, original-to-residue place/Picard specialization and prime-to-residue torsion injectivity remain. Actions on residue places alone do not prove inertia or the Frobenius quadratic on the original Picard Tate module. Parabolic character realization, exceptional primes, coefficient-field realization, original all-weight characteristic-zero association, automorphy and literal higher continuation remain. 16/20; DUB17--20 OPEN.',
'''+s[b:]
s=s.replace('source-gamma-one-residue-frobenius-audit-route-1287', 'source-gamma-one-residue-places-audit-route-1291')
s=s.replace("'(1, 9, 16)'", "'(3, 14, 18)'")
s=s.replace("'== 1'", "'== 3'").replace("'linterScopes=1'", "'linterScopes=3'")
s=s.replace("'modules=1'", "'modules=3'").replace("'all 16 required'", "'all 18 required'")
s=s.replace("'requiredProofValueEdges=16'", "'requiredProofValueEdges=18'")
s=s.replace("'proofEdges=16'", "'proofEdges=18'").replace("'queries=9'", "'queries=14'")
s=s.replace('record_gamma_one_residue_frobenius_1287', 'record_gamma_one_residue_places_1291')
s=s.replace('audit_gamma_one_residue_frobenius_1287', 'audit_gamma_one_residue_places_1291')
s=s.replace('dict(modules=1,queries=9,edges=16)', 'dict(modules=3,queries=14,edges=18)')
ast.parse(s)
out=p/'prepare_gamma_one_residue_places_audit_1291_generated.py'
assert not out.exists()
out.write_text(s,encoding='utf-8')
print(str(out))
