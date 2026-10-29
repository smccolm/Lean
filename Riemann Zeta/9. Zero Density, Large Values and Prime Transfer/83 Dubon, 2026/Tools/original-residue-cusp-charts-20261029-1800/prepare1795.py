from pathlib import Path
import json,re
d=Path('E:/Lean/.tmp/dubon83');p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
specs=[('HopfSubgroupVanishingAntipode', 'hopfSubgroupVanishingIdeal_counit', 'hinj X a ha', True)]
out='\n'
for mod,name,args,vars in specs:
 source=(p/f'Extension/Dubon2026/{mod}.lean').read_text(encoding='utf8')
 a=re.search(r'^theorem '+re.escape(name)+r'(?=[\s:{(\[])',source,re.M).start()
 depth=0;b=a
 while b < len(source):
  if depth==0 and source.startswith(':= by',b):break
  if source[b] in '([{':depth+=1
  elif source[b] in ')]}':depth-=1
  b+=1
 assert b<len(source),name
 sig=source[a:b].replace('theorem '+name,'theorem actual_hopf_subgroup_vanishing_antipode_'+name+'_source',1)
 doc_start=source.rfind('/--',0,a)
 prior=source[:doc_start].rstrip().splitlines()[-1]
 local_omit=prior+'\n' if prior.startswith('omit ') and prior.endswith(' in') else ''
 out+='section\n\nopen IsDedekindDomain Matrix Module\nopen scoped TensorProduct NumberField nonZeroDivisors\n\n'
 out+=''.join(line+'\n' for line in re.findall(r'^universe .+$',source,re.M))+'\n'
 if vars:
  out+='\n\n'.join(re.findall(r'^variable [\s\S]*?(?=\n\n)',source[:doc_start],re.M))+'\n\n'
 out+='/-- The same original Hopf point group in the exact subgroup vanishing consumer. -/\nnoncomputable local instance hopfSubgroupPointGroupSource : Group (WithConv (A →ₐ[R] K)) :=\n  commutativeHopfPointsGroup\n\n'
 out+=local_omit+f'/-- Exact original-object consumer of `{name}`. -/\n'+sig+':=\n  '+name+' '+args+'\n\nend\n\n'
(d/'consumers1795.txt').write_text(out,encoding='utf8')
(d/'modules1795.json').write_text(json.dumps(list(dict.fromkeys(x[0] for x in specs)),indent=2)+'\n',encoding='utf8')
print('Prepared one exact consumer: hopfSubgroupVanishingIdeal_counit.')
