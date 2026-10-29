from pathlib import Path
p=Path(__file__).parent
s=(p/'fetch_lana_reuse_1432.py').read_text(encoding='utf-8').replace("'lana-reuse-1432'","'lana-reuse-1432b'")
t=p/'fetch_lana_reuse_1432b.py';assert not t.exists();t.write_text(s,encoding='utf-8')
