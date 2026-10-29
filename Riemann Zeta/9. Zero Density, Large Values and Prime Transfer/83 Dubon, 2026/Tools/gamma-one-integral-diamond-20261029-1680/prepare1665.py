from pathlib import Path
import json,re
d=Path('E:/Lean/.tmp/dubon83');p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
specs=[('ArithmeticUnramifiedMatrixSpanning', 'arithmeticUnramifiedRepresentation_stabilizer_scalar_unit', 'a ha p hp hpa σ hσ δ hδ P hP U hU', True)]
out='\n'
for mod,name,args,vars in specs:
 source=(p/f'Extension/Dubon2026/{mod}.lean').read_text(encoding='utf8')
 a=re.search(r'^theorem '+re.escape(name)+r'(?=[\s:{(\[])',source,re.M).start()
 b=source.index(':= by', a)
 assert b < source.index('\nend\nend Dubon2026', a),name
 sig=source[a:b].replace('theorem '+name,'theorem actual_arithmetic_unramified_matrix_spanning_'+name+'_source',1)
 doc_start=source.rfind('/--',0,a)
 prior=source[:doc_start].rstrip().splitlines()[-1]
 local_omit=prior+'\n' if prior.startswith('omit ') and prior.endswith(' in') else ''
 out+='section\n\nopen IsDedekindDomain Matrix Module\nopen scoped TensorProduct NumberField nonZeroDivisors\n\n'
 out+=''.join(line+'\n' for line in re.findall(r'^universe .+$',source,re.M))+'\n'
 if vars:
  out+='\n\n'.join(re.findall(r'^variable [\s\S]*?(?=\n\n)',source[:doc_start],re.M))+'\n\n'
 out+=local_omit+f'/-- Exact original-object consumer of `{name}`. -/\n'+sig+':=\n  '+name+' '+args+'\n\nend\n\n'
(d/'consumers1665.txt').write_text(out,encoding='utf8')
(d/'modules1665.json').write_text(json.dumps(list(dict.fromkeys(x[0] for x in specs)),indent=2)+'\n',encoding='utf8')
print('Prepared one exact consumer: arithmeticUnramifiedRepresentation_stabilizer_scalar_unit.')
