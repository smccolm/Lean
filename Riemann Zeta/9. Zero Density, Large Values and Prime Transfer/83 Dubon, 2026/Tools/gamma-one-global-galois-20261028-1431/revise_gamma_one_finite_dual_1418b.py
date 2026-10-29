from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneFiniteTateDual1418a.lean';assert f.with_suffix('.exit').read_text().strip()=='1'
s=f.read_text(encoding='utf-8')
s=s.replace('variable (Q p n w : ℕ)', '''private theorem tate_map_eq_of_proj_eq {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p r : ℕ) [Fact p.Prime] [Module ℤ_[p] B]
    (φ : TateModule p A →ₗ[ℤ_[p]] B) {x y : TateModule p A}
    (hxy : TateModule.proj p A r x = TateModule.proj p A r y)
    (hzero : ∀ v : B, (p : ℤ_[p]) ^ r • v = 0) : φ x = φ y := by
  have hz : TateModule.proj p A r (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  apply sub_eq_zero.mp
  rw [← map_sub, ← TateModule.pow_smul_shiftOfProjEqZero r (x - y) hz, map_smul]
  exact hzero _

variable (Q p n w : ℕ)''')
s=s.replace('  let b :=', '  letI : Finite V := Module.finite_of_finite (ZMod N)\n  let b :=',1)
start=s.index('  have hz : TateModule.proj p J')
s=s[:start]+'''  apply tate_map_eq_of_proj_eq p (n + 1) φ hxy
  intro v
  rw [← IsScalarTower.algebraMap_smul (ZMod N)]
  simp only [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_smul]

end
end Dubon2026.SourceFunctionField.GammaOne
'''
t=p/'SourceGammaOneFiniteTateDual1418b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_finite_tate_dual_1418.ps1').read_text(encoding='utf-8').replace('1418a','1418b')
t=p/'build_gamma_one_finite_tate_dual_1418b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
