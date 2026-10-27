from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'fricke-cusp-descent-inputs-reuse-678/P2M/Sol/S_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range.lean.txt').read_text(encoding='utf-8')
a=s[s.index('theorem exists_algEquiv_apply_ne_of_exists_notMem'):s.index('open MvPolynomial Polynomial in')]
b=s[s.index('theorem exists_intermediateField_isAlgebraic_notMem_of_isAlgebraic'):s.index('end WLightR11g')]
head='''import SourcePureTranscendentalConstantIntersection

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> fixed-field descent of the proved twist-stable cusp image. Every
coefficient outside the original characteristic-zero field is moved by an
automorphism of the algebraically closed ambient field. Algebraic and
transcendental coefficients are separated using actual intermediate fields
and the native infinite Galois fixed-field theorem. Adapted from
anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range. -/
namespace Dubon2026.SourceFunctionField.ConstantFixedField
noncomputable section
open IntermediateField

'''
last='''theorem mem_range_of_fixed {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsAlgClosed E] [CharZero F] {c : E}
    (hfix : ∀ σ : E ≃ₐ[F] E, σ c = c) : ∃ a : F, algebraMap F E a = c := by
  by_contra hn
  have hc : c ∉ (⊥ : IntermediateField F E) := fun h => hn (IntermediateField.mem_bot.mp h)
  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_ne hc
  exact hσ (hfix σ)

end
end Dubon2026.SourceFunctionField.ConstantFixedField
'''
f=p/'SourceAlgebraicallyClosedFixedField.lean';assert not f.exists();f.write_text(head+a+b+last,encoding='utf-8')
print('Prepared coefficient separation and the full original-field fixed-coefficient conclusion')