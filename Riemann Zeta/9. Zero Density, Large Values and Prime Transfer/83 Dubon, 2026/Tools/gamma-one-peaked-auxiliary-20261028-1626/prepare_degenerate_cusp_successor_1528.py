from pathlib import Path
s=Path(__file__).parent;a=s/'SourceIntegralTraceDegenerateCusp1527a.lean';b=s/'SourceIntegralTraceDegenerateCusp1527b.lean'
assert not b.exists()
t=a.read_text(encoding='utf-8').replace('  rw [← SlashAction.slash_mul, mul_inv_cancel_right, ModularForm.SL_slash,', '  simp only at hGS\n  rw [← SlashAction.slash_mul, mul_inv_cancel_right, ModularForm.SL_slash,')
b.write_text(t,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
