from pathlib import Path
p=Path(__file__).parent
s=(p/'fetch_curve_reuse_1283b.py').read_text(encoding='utf-8')
s=s.replace("'curve-reuse-1283b'","'lana-reuse-1432'")
s=s.replace("keys=['modularcurve','gamma1','goodreduction','jacobian','tatespecial','neron','picard','eichler','satotate','automorph','galoisrep','symmetricpower']", "keys=['modularcurve','gamma1','goodreduction','jacobian','torsion','neron','picard','weierstrass','reduction','uniformization','pairing','specialization','flat','proper','smooth']")
s=s.replace("[('CBirkbeck/AINTLIB','main'),('CBirkbeck/AINTLIB','dev/modular-curves'),('facebookresearch/atlas-lean','main')]", "[('lana-agents/iut','main'),('lana-agents/elliptic-reduction','main'),('lana-agents/elliptic-curves','main'),('lana-agents/tate-curves-theta','main')]")
t=p/'fetch_lana_reuse_1432.py';assert not t.exists();t.write_text(s,encoding='utf-8')
