from pathlib import Path
import ast
p=Path(__file__).parent
s=(p/'prepare_gamma_one_residue_frobenius_audit_1287.py').read_text(encoding='utf-8')
s=s.replace("mods=['SourceGammaOneResidueFrobenius']", "mods=['SourceGammaOnePrimeHeckeIndex','SourceGammaOneSignedHeckeIndex','SourceGammaOneHeckeCoordinateDegree','SourceGammaOneHeckePrimeDegree']\nev=dict(zip(mods,['1293b','1294a','1295a','1296d'],strict=True))")
s=s.replace("cn='Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.'", "cn='Dubon2026.SourceFunctionField.GammaOne.'")
s=s.replace("m+'1286d.exit'", "m+ev[m]+'.exit'").replace("m+'1286d.log'", "m+ev[m]+'.log'")
a=s.index('roots=[cn+x');b=s.index('prev=json.loads',a)
s=s[:a]+'''roots=[cn+'heckeAlpha_finrank']
edges=ths+defs+[cn+x for x in ['finrank_over_j_eq_index',
 'HeckeFiberOrbits.finrank_over_j_eq_index','finite_rational_coordinate',
 'gamma1_hecke_baseChange_le']]+[
 'Dubon2026.SourceFunctionField.DegreeTransport.relfinrank_eq_of_finite',
 'Dubon2026.sourcePrincipalReduction_surjective',
 'Dubon2026.SourceLevelProjective.gamma0_index',
 'Dubon2026.SourceLevelProjective.dedekindPsi_prime']
'''+s[b:]
s=s.replace("localModules=prev['localModules']+mods", "localModules=mods")
s=s.replace("compileEvidence={m:m+'1286d' for m in mods}", "compileEvidence={m:m+ev[m] for m in mods}")
s=s.replace('(8,1,16)','(14,0,22)')
s=s.replace("stem='source-gamma-one-residue-frobenius-1'", "stem='source-gamma-one-hecke-degree-1'")
s=s.replace("new='SourceGammaOneResidueFrobenius'", "new='SourceGammaOneHeckeDegree'")
s=s.replace("'ScratchOwnership1287'", "'ScratchOwnership1297'")
s=s.replace('GAMMA ONE RESIDUE FROBENIUS','GAMMA ONE HECKE DEGREE')
a=s.index("  s=s[:start]+' occur in the ");b=s.index("+s[end:]",a)+len("+s[end:]")
s=s[:a]+'''  s=s[:start]+' occur in the proof value closure of the actual Gamma1 alpha inclusion degree p+1, consuming native coprime principal lifting, signed subgroup indices, complex j-fiber degrees and Laurent coefficient-field degree transport. The explicit embedding census and norm identity, residue degree preservation and original Picard specialization remain unresolved'+s[end:]'''+s[b:]
a=s.index("reuse=[r/'Extension");b=s.index('route=dict(',a)
s=s[:a]+'''reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in [
 'SourcePrincipalCoprimeReduction','SourceLevelProjectiveCosets','SourceLevelIndexFormula',
 'SourceLevelPsiPrimeStep','SourceGammaOnePlusMinus','SourceGammaOneExactRamification',
 'SourceGammaOneHeckeJDegree','SourceGammaOneDegreeBaseChange','SourceLaurentDegreeTransport',
 'SourceOriginalHeckePrimeDegree','SourceOriginalHeckeEmbeddingCensus',
 'SourceGammaOneHeckeFieldFinite']]
'''+s[b:]
a=s.index(' chain=');b=s.index(' externalBuild=',a)
s=s[:a]+''' chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 geometric Tate Frobenius -> actual original Hecke norm reduction -> complete original embedding census -> exact original alpha inclusion degree p+1.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='Existing principal-level lifting gives surjectivity modulo a coprime prime for the actual Gamma1 group. Pulling back the native Borel identifies the literal lower correspondence subgroup. The proved Gamma0 index gives p+1, also after adjoining central negative identity. Existing complex j-fiber degrees and Laurent base-change degree transport then identify the two original coordinate degrees. Native relative-degree multiplicativity and the signed index ratio prove the actual alpha inclusion degree. Explicit Algebra.toModule selects the actual inclusion scalar action and avoids typeclass normalization without raising limits. No new projective-line count, modular polynomial or Atkin hypothesis is introduced.',
 assumptionsToDischarge=[
 'At every nonzero level M and prime p coprime to M, the original Gamma1 lower Hecke subgroup has relative index p+1, with the same exact relative index after the required central-sign enlargement.',
 'The j-coordinate degrees of both original fields equal their signed subgroup indices over every characteristic-zero coefficient field.',
 'The original alpha field inclusion has degree p+1 under its actual scalar action, removing the dimension input for a complete p+1 embedding census.'],
 remaining='The exact field degree does not construct the explicit conjugate embeddings or prove their values on the second Hecke map. The original Gamma1 norm identity with its diamond convention, residue degree equality, genus preservation, original-to-residue place/Picard specialization and torsion injectivity remain. Consequently the original geometric Tate quadratic/inertia, parabolic character realization, exceptional primes, coefficient-field realization, original all-weight characteristic-zero association, automorphy and literal higher continuation remain. 16/20; DUB17--20 OPEN.',
'''+s[b:]
s=s.replace('source-gamma-one-residue-frobenius-audit-route-1287', 'source-gamma-one-hecke-degree-audit-route-1297')
s=s.replace("'(1, 9, 16)'", "'(4, 14, 22)'")
s=s.replace("'== 1'", "'== 4'").replace("'linterScopes=1'", "'linterScopes=4'")
s=s.replace("'modules=1'", "'modules=4'").replace("'all 16 required'", "'all 22 required'")
s=s.replace("'requiredProofValueEdges=16'", "'requiredProofValueEdges=22'")
s=s.replace("'proofEdges=16'", "'proofEdges=22'").replace("'queries=9'", "'queries=14'")
s=s.replace('record_gamma_one_residue_frobenius_1287', 'record_gamma_one_hecke_degree_1297')
s=s.replace('audit_gamma_one_residue_frobenius_1287', 'audit_gamma_one_hecke_degree_1297')
s=s.replace('dict(modules=1,queries=9,edges=16)', 'dict(modules=4,queries=14,edges=22)')
ast.parse(s)
out=p/'prepare_gamma_one_hecke_degree_audit_1297_generated.py'
assert not out.exists();out.write_text(s,encoding='utf-8')
print(str(out))
