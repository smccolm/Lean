from pathlib import Path
import json,re
d=Path('E:/Lean/.tmp/dubon83');p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
specs=[('FractionalIdealPowerRoots', 'fractionalIdealCountRootUnit_pow', 'n I hdiv', True), ('PrincipalIdealValuationBridge', 'emptySelmer_mem_iff_principal_counts', 'n x', True)]
out='\n'
for mod,name,args,vars in specs:
 source=(p/f'Extension/Dubon2026/{mod}.lean').read_text(encoding='utf8')
 a=re.search(r'^theorem '+re.escape(name)+r'(?=[\s:{(\[])',source,re.M).start()
 depth=0;b=a
 while b < len(source):
  if depth==0 and source.startswith(':=',b):break
  if source[b] in '([{':depth+=1
  elif source[b] in ')]}':depth-=1
  b+=1
 assert b<len(source),name
 sig=source[a:b].replace('theorem '+name,'theorem actual_selmer_ideal_root_'+name+'_source',1)
 doc_start=source.rfind('/--',0,a)
 prior=source[:doc_start].rstrip().splitlines()[-1]
 local_omit=prior+'\n' if prior.startswith('omit ') and prior.endswith(' in') else ''
 out+='section\n\nopen IsDedekindDomain Matrix Module\nopen scoped TensorProduct NumberField nonZeroDivisors\n\n'
 out+=''.join(line+'\n' for line in re.findall(r'^universe .+$',source,re.M))+'\n'
 if vars:
  a=re.search(r'^variable ',source,re.M).start();b=source.index('/--',a);out+=re.sub(r"^omit .+ in\n", "", source[a:b], flags=re.M)
 out+=local_omit+f'/-- Exact original-object consumer of `{name}`. -/\n'+sig+':=\n  '+name+' '+args+'\n\nend\n\n'
(d/'consumers1512.txt').write_text(out,encoding='utf8')
(d/'modules1512.json').write_text(json.dumps(list(dict.fromkeys(x[0] for x in specs)),indent=2)+'\n',encoding='utf8')
print('Prepared two exact consumers of actual fractional-ideal roots and original Selmer multiplicity normalization.')
