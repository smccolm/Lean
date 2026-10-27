from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'SourceFrickeEllipticDivisibilityTwist.lean').read_text(encoding='utf-8')
body=s[s.index('  obtain ⟨G, hG, he⟩ := hdiv'):s.index('\nend\nend Dubon2026.SourceFricke')]
body=body.replace('(frickeSpanPow N F p : ℍ → ℂ)','(F ^ p : ℍ → ℂ)').replace('(frickeCoefficientTwist N σ F : ℍ → ℂ)',"(F' : ℍ → ℂ)")
a=body.index("  obtain ⟨W', hW', ht⟩");b=body.index("  refine ⟨W'",a)
body=body[:a]+'''  obtain ⟨W', hW', ht⟩ := (hFF'.pow p).holomorphic_division (hJJ.pow q)
    ((cyclotomicHolomorphicFrickeAlgebra N).pow_mem hF p)
    ((cyclotomicHolomorphicFrickeAlgebra N).pow_mem hF' p) Jq.property hJq0 hW hrel
'''+body[b:]
header='''import SourceCyclotomicHolomorphicDivision

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> elliptic divisibility under nontrivial cyclotomic conjugation.
Reuse the already proved source power identities and holomorphic division
inside the original fraction algebra. The actual conjugate satisfies the
same E4/E6 divisibility conditions; no new growth premise is introduced. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold

theorem CyclotomicConjugates.elliptic_divisibility
    {N : ℕ} [NeZero N] {σ : kN N ≃ₐ[ℚ] kN N} {F F' : ℍ → ℂ}
    (hFF' : CyclotomicConjugates σ F F')
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N)
    (hF' : F' ∈ holomorphicCyclotomicFrickeFractions N)
    (J : (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule) (hJ0 : (J : ℍ → ℂ) ≠ 0)
    (hJJ : CyclotomicConjugates σ (J : ℍ → ℂ) (J : ℍ → ℂ))
    (E : ℍ → ℂ) (m p q : ℕ)
    (hEJ : ∀ τ : ℍ, E τ ^ p = (J : ℍ → ℂ) τ * CuspForm.discriminant τ)
    (hdiv : ∃ G : ℍ → ℂ, MDiff G ∧ ∀ τ : ℍ,
      (F τ * CuspForm.discriminant τ ^ m) ^ p = E τ ^ (p * q) * G τ) :
    ∃ G' : ℍ → ℂ, MDiff G' ∧ ∀ τ : ℍ,
      (F' τ * CuspForm.discriminant τ ^ m) ^ p = E τ ^ (p * q) * G' τ := by
'''
f=p/'SourceCyclotomicEllipticDivisibility.lean';assert not f.exists();f.write_text(header+body+'\n\nend\nend Dubon2026.SourceFricke\n',encoding='utf-8')
print('Prepared actual elliptic-divisibility consumer by reusing the proved power identities')
