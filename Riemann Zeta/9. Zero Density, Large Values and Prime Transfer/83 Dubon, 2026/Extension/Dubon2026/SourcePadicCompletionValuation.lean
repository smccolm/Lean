import Dubon2026.SourceReductionCompletionPadicMap

/-! DUB-17/18 -> prescribed residual association -> valuation compatibility.
The native rational completion equivalence identifies the actual integer
rings, so no isometry between differently normalized adic norms is needed. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable (ell : ℕ) (hell : ell.Prime) [Fact ell.Prime]
local notation "v" => Equiv.symm (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (Subtype.mk ell hell)

theorem sourcePadicCompletionEquiv_mem_integer (x : ℚ_[ell]) :
    Padic.adicCompletionEquiv (𝓞 ℚ) ⟨ell, hell⟩ x ∈ (v).adicCompletionIntegers ℚ ↔
      ‖x‖ ≤ 1 := by
  let e := Padic.adicCompletionEquiv (𝓞 ℚ) ⟨ell, hell⟩
  let ei := PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨ell, hell⟩
  constructor
  · intro hx
    let y : (v).adicCompletionIntegers ℚ := ⟨e x, hx⟩
    have heq : ((ei.symm y : ℤ_[ell]) : ℚ_[ell]) = x := by
      rw [PadicInt.coe_adicCompletionIntegersEquiv_symm_apply]
      exact e.symm_apply_apply x
    have hn := (ei.symm y).property
    rwa [heq] at hn
  · intro hx
    let z : ℤ_[ell] := ⟨x, hx⟩
    have heq : ((ei z : (v).adicCompletionIntegers ℚ) : (v).adicCompletion ℚ) = e x :=
      PadicInt.coe_adicCompletionIntegersEquiv_apply (𝓞 ℚ) ⟨ell, hell⟩ z
    rw [← heq]
    exact (ei z).property

end
end Dubon2026
