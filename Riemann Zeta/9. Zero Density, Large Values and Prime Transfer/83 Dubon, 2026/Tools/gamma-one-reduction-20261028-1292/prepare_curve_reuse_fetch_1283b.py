from pathlib import Path
p=Path(__file__).parent
s=(p/'fetch_curve_reuse_1283.py').read_text(encoding='utf-8').replace("/'curve-reuse-1283'", "/'curve-reuse-1283b'")
f=p/'fetch_curve_reuse_1283b.py';assert not f.exists();f.write_text(s,encoding='utf-8')
