from pathlib import Path
s=Path(__file__).parent
c=(s/'prepare_gamma_one_diamond_canonical_1441.py').read_text(encoding='utf-8')
c=c.replace("'SourceGammaOneArithmeticDiamond':'1434b'","'SourceGammaOneArithmeticDiamondPolynomial':'1434b'")
c=c.replace('pending=[]',"aliases={'SourceGammaOneArithmeticDiamondPolynomial':'SourceGammaOneArithmeticDiamond'}\npending=[]")
c=c.replace("f=s/(m+v+'.lean')","f=s/(aliases.get(m,m)+v+'.lean')")
c=c.replace("'import '+nm+ver+'\\n'","'import '+aliases.get(nm,nm)+ver+'\\n'")
c=c.replace("t=s/'gamma-one-diamond-versions-1441.json'", "t=s/'gamma-one-diamond-version-aliases-1441.json';assert not t.exists();pending.append((t,json.dumps(aliases,indent=2)+'\\n'))\nt=s/'gamma-one-diamond-versions-1441.json'")
t=s/'prepare_gamma_one_diamond_canonical_1441b.py';assert not t.exists();t.write_text(c,encoding='utf-8')
c=(s/'prepare_gamma_one_diamond_audit_1442.py').read_text(encoding='utf-8')
t=s/'prepare_gamma_one_diamond_audit_1442b.py';assert not t.exists();t.write_text(c,encoding='utf-8')
print('Preserve the existing arithmetic-diamond module; use the distinct new arithmetic-diamond-polynomial name.')
