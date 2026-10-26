from pathlib import Path
import json
p=Path(__file__).parent
c=json.loads('{"context": "    (hT : ModularGroup.T \\u2208 \\u0393) :\\n    FiniteDimensional", "newcontext": "    (hT : ModularGroup.T \\u2208 \\u0393) :\\n    letI : Algebra \\u211a (qExpFunctionFieldC \\u211a \\u0393) := (qExpFunctionFieldC \\u211a \\u0393).algebra\'\\n    FiniteDimensional", "start": "  classical\\n  let F := qExpFunctionFieldC \\u211a \\u0393", "newstart": "  classical\\n  letI : Algebra \\u211a (qExpFunctionFieldC \\u211a \\u0393) := (qExpFunctionFieldC \\u211a \\u0393).algebra\'\\n  let F := qExpFunctionFieldC \\u211a \\u0393", "start2": "  haveI := finiteDimensional_jCoordinate hT", "newstart2": "  letI : Algebra \\u211a (qExpFunctionFieldC \\u211a \\u0393) := (qExpFunctionFieldC \\u211a \\u0393).algebra\'\\n  haveI := finiteDimensional_jCoordinate hT"}')
for name, pairs in [('SourceGammaOneFunctionFieldFinite', [('context','newcontext'),('start','newstart')]), ('SourceGammaOneFunctionFieldBaseChange', [('start2','newstart2')])]:
 f=p/(name+'.lean'); t=f.read_text(encoding='utf-8')
 for a,b in pairs:
  assert c[a] in t; t=t.replace(c[a],c[b],1)
 f.write_text(t,encoding='utf-8')
