from pathlib import Path
import ast
p=Path(__file__).parent
s=(p/'register_additional_reuse_1263.py').read_text(encoding='utf-8')
s=s.replace("   assert sha(folder/row['path'])==row['sha256'],row['path']",
 "   if row.get('status')==404:\n    assert row['path']=='LICENSE.txt' and not (folder/row['path']).exists()\n    assert meta['repository']=='tomdif/eml-lean'\n   else:\n    assert sha(folder/row['path'])==row['sha256'],row['path']")
s=s.replace("'fetch_followup_candidates_1251c.py','register_additional_reuse_1263.py'",
 "'fetch_followup_candidates_1251c.py','register_additional_reuse_1263.py',\n 'register_additional_reuse_1263b.py','prepare_additional_reuse_registration_1263b.py'")
s=s.replace("projectPinsChanged=False,files=rows", "registrationRetry='First registration stopped before mutation on the explicitly recorded optional LICENSE HTTP 404. This successor verifies that precise absence and hashes every successfully fetched file.',projectPinsChanged=False,files=rows")
ast.parse(s)
out=p/'register_additional_reuse_1263b.py';assert not out.exists()
out.write_text(s,encoding='utf-8')
