from pathlib import Path
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
assert (p/'SourceSupportedCharacterFiber1170b.exit').read_text().strip()=='0'
assert (p/'SourceSupportedCharacterFiber1170b.log').stat().st_size==0
s=(r/'SourceFaithfulCharacterDivisibility.lean').read_text(encoding='utf-8')
s=s.replace('import Dubon2026.SourceFaithfulCharacterFiber','import SourceSupportedCharacterFiber')
s=s.replace('sourceFaithfulCharacter_div_isIntegral','sourceSupportedCharacter_div_isIntegral')
s=s.replace('[Module.Finite \u2124 M] [FaithfulSMul A M]','[Module.Finite \u2124 M]')
s=s.replace('(\u03c7 : A \u2192+* F) (t : A)', '(\u03c7 : A \u2192+* F) (hann : Module.annihilator A M \u2264 RingHom.ker \u03c7) (t : A)')
s=s.replace('sourceFaithfulModule_nontrivial_characterFiber','sourceModule_nontrivial_characterFiber_of_annihilator hann')
s=s.replace('In a finite faithful module','In a finite module supported at the prescribed character')
s=s.replace('Reuse the actual nonzero faithful character fiber','Reuse the actual nonzero supported character fiber')
f=p/'SourceSupportedCharacterDivisibility.lean';assert not f.exists();f.write_text(s,encoding='utf-8')
