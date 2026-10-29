from pathlib import Path
p=Path(__file__).parent
s=(p/'fetch_lana_candidates_1432c.py').read_text(encoding='utf-8')
s=s.replace("'lana-reuse-1432c'","'lana-reuse-1432d'")
s=s.replace("assert not tree.get('truncated',False)","assert not tree.get('truncated',False) or repo=='anthropics/fermats-last-theorem'")
s=s.replace('files=rows,externalBuild=False',"files=rows,inventoryBoundary='The four new LANA trees are complete. The older Anthropic inventory is truncated: only two explicitly present paths were selected, with no absence inference from that inventory.',externalBuild=False")
t=p/'fetch_lana_candidates_1432d.py';assert not t.exists();t.write_text(s,encoding='utf-8')
