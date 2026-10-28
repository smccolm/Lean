from pathlib import Path
import json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
lines=(p/'gamma-one-period-core-reuse-796/S_ModularCurve_Period_exists_parabolicHoms_int_castAddHom_comp_eq_of_forall_isOfFinOrder.lean.txt').read_text(encoding='utf-8').splitlines()
b1='open Matrix.SpecialLinearGroup ModularGroup\n\n'
b1+='theorem neg_one_mem_center : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) :=\n  (SourceModularFreeProduct.mem_center_iff_eq _).mpr (Or.inr rfl)\n\n'
b1+='theorem eq_one_or_eq_neg_one_of_mem_center {z : SL(2, ℤ)} (hz : z ∈ Subgroup.center SL(2, ℤ)) :\n    z = 1 ∨ z = -1 := (SourceModularFreeProduct.mem_center_iff_eq z).mp hz\n\n'
b1+='\n'.join(lines[585:596])+'\n'
b2='\n'.join(lines[705:765])+'\n'
a='\n'.join(lines[744:749])
b='''  obtain ⟨ε, δ, k, hε, hγ⟩ := SourceParabolic.classification γ h
  refine ⟨ρ δ, k, ?_⟩
  have hε0 : ρ ε = 1 := by
    rcases hε with rfl | rfl
    · exact map_one ρ
    · exact (hker _).mpr neg_one_mem_center
  rw [hγ, map_mul, hε0, one_mul, map_mul, map_mul, map_zpow, map_inv, hT]'''
assert a in b2;b2=b2.replace(a,b).replace('omit hker in\ninclude hker in\n\n','')
body='\n'.join(lines[775:873])+'\n'
body=body.replace('  obtain ⟨e, he0, he1⟩ := ModularGroup.exists_mulEquiv_freeProduct_quotient_center','  let e := SourceModularFreeProduct.mulEquiv\n  have he0 := SourceModularFreeProduct.mulEquiv_of_zero\n  have he1 := SourceModularFreeProduct.mulEquiv_of_one')
body=body.replace('MulEquiv.symm_apply_eq, tP, map_mul','MulEquiv.symm_apply_eq, tP, SourceCuspCorrection.τ, map_mul')
body=body.replace('(φ : Additive Γ →+ ZMod n)', 'φ').replace('φ.2 γ','hpar γ')
body=body.replace('have hxpar : ModularCurve.Period.IsParabolicHom Γ x := by','have hxpar : ∀ γ : Γ, γ.val.val.trace ^ 2 = 4 → x (Additive.ofMul γ) = 0 := by')
body=body.replace('  refine ⟨⟨x, hxpar⟩, ?_⟩','  refine ⟨x, hxpar, ?_⟩')
sig='''open Matrix.SpecialLinearGroup ModularGroup

/-- Every finite-index integral modular subgroup admits an integral parabolic lift
of a finite-valued parabolic character that vanishes on finite-order elements. -/
theorem exists_int_lift (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (n : ℕ)
    (φ : Additive Γ →+ ZMod n)
    (hpar : ∀ γ : Γ, γ.val.val.trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0)
    (hφ : ∀ γ : Γ, IsOfFinOrder γ → φ (Additive.ofMul γ) = 0) :
    ∃ x : Additive Γ →+ ℤ,
      (∀ γ : Γ, γ.val.val.trace ^ 2 = 4 → x (Additive.ofMul γ) = 0) ∧
      (Int.castAddHom (ZMod n)).comp x = φ := by
'''
for mod,imports,body in [
 ('SourceIntegralCharacterModularFacts',['SourceIntegralCharacterCorrection','SourceModularFreeProduct','Dubon2026.SourceParabolicClassification'],b1),
 ('SourceIntegralCharacterModularBridge',['SourceIntegralCharacterModularFacts'],b2),
 ('SourceIntegralParabolicCharacterLift',['SourceIntegralCharacterModularBridge'],sig+body)]:
 header=''.join('import '+i+'\n' for i in imports)+'\n/-! DUB-17/18 -> original all-weight association -> Gamma1 Picard/H1\n-> Abel-Jacobi -> unitary multiplier logarithms -> integral parabolic-character\nlifting. Adapted from the Apache-2.0 scope-796 primary at revision\n6e837e75355538c7f80bab5b956861e86c4eacc2. Reuse the repository\nSourceParabolic.classification and the audited actual projective free-product\nequivalence. The theorem uses literal squared-trace-four vanishing, all finite\nindices and all natural moduli, including zero. It assumes no lifting theorem. -/\nnamespace Dubon2026.SourceIntegralCharacterLift\nnoncomputable section\nopen Subgroup\nopen scoped MatrixGroups\n'
 with (p/(mod+'.lean')).open('x',encoding='utf-8',newline='\n') as out:out.write(header+body+'\nend\nend Dubon2026.SourceIntegralCharacterLift\n')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[r/'SourceParabolicClassification.lean',p/'SourceModularProjectiveKernel.lean',p/'SourceModularFreeProduct.lean',p/'source-modular-free-product-1-scratch-receipt.json']
with (p/'gamma-one-integral-character-modular-route-826.json').open('x',encoding='utf-8') as out:json.dump(dict(chain='DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1 -> Abel-Jacobi -> unitary logarithms -> integral parabolic-character lifting -> actual modular-group transport.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse the existing signed trace-four classification and audited scalar-center characterization; do not duplicate primary integer matrix/coprime fixed-vector arguments. Consume the actual generator-preserving C2*C3 equivalence, initial scalar Shapiro lift, native transfer cusp sum and audited cusp correction.',assumptionsToDischarge='Derive the actual integral parabolic lift for every finite-index subgroup of SL2(Z), every natural modulus n including zero, and every ZMod n character that is parabolic and vanishes on finite-order elements. No presentation, character lift, divisibility correction or parabolic classification premise remains.',remaining='Unitary real logarithms, analytic reciprocity, Abel-Jacobi, original all-weight arithmetic association and full DUB17--20 closure remain.'),out,indent=2);out.write('\n')
print('Prepared original modular-group transport using existing trace-four classification.')
