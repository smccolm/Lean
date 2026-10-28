from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
lines=(p/'gamma-one-period-core-reuse-795b/S_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex.lean.txt').read_text(encoding='utf-8').splitlines()
body='\n'.join(l[2:] if l.startswith('  ') else l for l in lines[277:333])+'\n'
body=body.replace('ModularCurve.Period.IsParabolicHom Γ Φ','∀ γ : Γ, γ.val.val.trace ^ 2 = 4 → Φ (Additive.ofMul γ) = 0')
old='''  obtain ⟨x, hx⟩ :=
    ModularCurve.Period.exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder Γ
      (p i₀ ^ e i₀) ⟨Φ, ModularCurve.Period.mem_parabolicHoms_iff.mpr hΦpar⟩ hΦfin'''
new='''  obtain ⟨x, hxpar, hx⟩ :=
    SourceIntegralCharacterLift.exists_int_lift Γ (p i₀ ^ e i₀) Φ hΦpar hΦfin'''
assert old in body;body=body.replace(old,new).replace('(x : Additive Γ →+ ℤ)','x').replace('(ModularCurve.Period.mem_parabolicHoms_iff.mp x.2) γ heq','hxpar γ heq')
b1='''variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
variable {n : ℕ} {ι : Type} {p e : ι → ℕ}

/-- Every cyclic torsion factor of the actual parabolic abelianization is trivial,
as proved by the integral lift of its coordinate character. -/
theorem torsion_exponent_eq_zero
    (eqv : Q Γ ≃+ (Fin n →₀ ℤ) × DirectSum ι (fun i => ZMod (p i ^ e i)))
    (hp : ∀ i, (p i).Prime) : ∀ i, e i = 0 := by
  classical
'''+body
b2='variable (Γ : Subgroup SL(2, ℤ))\n\n/-- The actual unit-circle character associated with a unit-modulus multiplier. -/\n'+'\n'.join(lines[252:265])+'\n'
b3='variable (Γ : Subgroup SL(2, ℤ))\n\n'+'\n'.join(lines[265:276])+'\n'
b3=b3.replace('theorem main','theorem exists_real_logarithm')
b3+='  have he : ∀ i, e i = 0 := torsion_exponent_eq_zero Γ eqv hp\n'+'\n'.join(lines[333:370])+'\n'
for mod,imports,body in [
 ('SourceUnitaryCharacterTorsion',['SourceUnitaryCharacterBasisExt'],b1),
 ('SourceUnitaryCircleCharacter',['SourceUnitaryCharacterTorsion'],b2),
 ('SourceUnitaryCharacterLogarithm',['SourceUnitaryCircleCharacter'],b3)]:
 header=''.join('import '+i+'\n' for i in imports)+'\n/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary\nmultiplier logarithms. Adapted from the Apache-2.0 scope-795b primary at\nrevision 6e837e75355538c7f80bab5b956861e86c4eacc2. The actual\nparabolic quotient has no cyclic torsion factors because each coordinate\ncharacter has the proved integer parabolic lift. The resulting logarithm\nis additive and vanishes on the same actual elliptic/parabolic elements.\nNo torsion-freeness, character lift, or logarithm premise is assumed. -/\nnamespace Dubon2026.SourceUnitaryCharacterLift\nnoncomputable section\nopen scoped MatrixGroups\n'
 with (p/(mod+'.lean')).open('x',encoding='utf-8',newline='\n') as out:out.write(header+body+'\nend\nend Dubon2026.SourceUnitaryCharacterLift\n')
print('Prepared torsion elimination and the actual real logarithm.')
