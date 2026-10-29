from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientWords1451b.lean';c=f.read_text(encoding='utf-8')
a=c.index('variable (hlarge :');b=c.index('\ntheorem binaryDiamondQuotientOriginalTransfer_word',a)
params=c[a:b].replace('variable ','    ')
c=c[:a]+c[b:]
c=c.replace('theorem binaryDiamondQuotientOriginalTransfer_word\n','theorem binaryDiamondQuotientOriginalTransfer_word\n'+params+'\n')
c=c.replace('theorem binaryDiamondQuotientOriginalTransfer_word_kernel\n','theorem binaryDiamondQuotientOriginalTransfer_word_kernel\n'+params+'\n')
t=s/'SourceGammaOneDiamondQuotientWords1451c.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
a=f.with_suffix('.lean.txt');assert not a.exists();f.rename(a)
print('Put dependent operator-family binders in each theorem signature, preserving all parameters.')
