import Dubon2026.SourceGammaOneCoverHeckeCosets

/-! DUB-17/18 -> original all-weight association -> exact joint arithmetic
realization -> primitive boundary Hecke trace. Reuse the already proved
native cover-coset equivalence and original Gamma0 transversal to count
the actual Gamma1 Hecke cosets. This is the total multiplicity required
to close the primitive two-orbit trace calculation. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup

/-- At every prime away from the original level, the actual Gamma1
upper-correspondence coset space has exactly ell plus one elements. -/
theorem gammaOne_prime_hecke_cosets_card (M ell : ℕ) [NeZero M]
    (hell : ell.Prime) (hcop : Nat.Coprime ell M) :
    Nat.card (Gamma1 M ⧸ sourceGammaOneHeckeUpper M ell) = ell + 1 := by
  letI : NeZero ell := ⟨hell.ne_zero⟩
  have he := Nat.card_congr
    (sourceGammaOneCoverHeckeCosetEquiv M 1 ell hell (by simpa using hcop))
  rw [show M * 1 ^ 2 = M by simp] at he
  rw [he, ← Nat.card_congr (heckeUpperCosetEquiv hell hcop)]
  rw [Nat.card_eq_fintype_card, Fintype.card_option, ZMod.card]

end
end Dubon2026.SourceFunctionField.GammaOne
