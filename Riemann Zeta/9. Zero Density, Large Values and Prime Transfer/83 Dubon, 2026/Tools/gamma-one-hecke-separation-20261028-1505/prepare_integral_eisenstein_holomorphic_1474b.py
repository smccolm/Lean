from pathlib import Path
s=Path(__file__).parent
a=s/'SourceIntegralEisensteinHolomorphic1474a.lean'
t=a.read_text(encoding='utf-8').replace('(fun (s : Finset (rows N a)) => ∑ x ∈ s, eisSummand 4 x ·)','(fun (s : Finset (rows N a)) (z : ℍ) => ∑ x ∈ s, eisSummand 4 x z)')
t=t.replace('  · simp only [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.top_eq_univ,\n      tendstoLocallyUniformlyOn_univ]','  · simp only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]')
a.rename(a.with_suffix('.lean.txt'))
with (s/'SourceIntegralEisensteinHolomorphic1474b.lean').open('x',encoding='utf-8') as h:h.write(t)
