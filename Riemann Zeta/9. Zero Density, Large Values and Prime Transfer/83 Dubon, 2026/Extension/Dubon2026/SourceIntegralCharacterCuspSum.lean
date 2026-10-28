import Dubon2026.SourceIntegralCharacterCuspConjugacy

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary
multiplier logarithms -> integral parabolic-character lifting. The native
transfer formula proves zero total cusp value; the audited actual edge-chain
correction then removes all parabolic values without changing reduction
modulo n. Adapted from the Apache-2.0 integral-lift primary in scope 796,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2.
The original modular-group transport remains a separate obligation. -/
namespace Dubon2026.SourceIntegralCharacterLift
noncomputable section
open Subgroup
section CuspGeneral
variable {G : Type} [Group G] (H : Subgroup G)
theorem sum_char_cuspGen_eq_zero [H.FiniteIndex] {t₁ t₂ : G} (h₁ : IsOfFinOrder t₁) (h₂ : IsOfFinOrder t₂)
    (χ : Additive H →+ ℤ) [Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers (t₁ * t₂)) (G ⧸ H)))] :
    ∑ q : Quotient (MulAction.orbitRel (Subgroup.zpowers (t₁ * t₂)) (G ⧸ H)),
      χ (Additive.ofMul ⟨q.out.out⁻¹ * (t₁ * t₂) ^ Function.minimalPeriod ((t₁ * t₂) • ·) q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem H (t₁ * t₂) q.out⟩) = 0 := by
  set f : H →* Multiplicative ℤ := AddMonoidHom.toMultiplicativeRight χ with hf
  have hfin : ∀ {s : G}, IsOfFinOrder s → f.transfer s = 1 := by
    intro s hs
    have := f.transfer.isOfFinOrder hs
    exact (isOfFinAddOrder_iff_eq_zero (G := ℤ) _).mp this
  have htr := f.transfer_eq_prod_quotient_orbitRel_zpowers_quot (t₁ * t₂)
  rw [map_mul, hfin h₁, hfin h₂, mul_one] at htr
  have := congrArg Multiplicative.toAdd htr
  rw [toAdd_one, toAdd_prod] at this
  rw [← this.symm]
  rfl
end CuspGeneral

end
end Dubon2026.SourceIntegralCharacterLift
