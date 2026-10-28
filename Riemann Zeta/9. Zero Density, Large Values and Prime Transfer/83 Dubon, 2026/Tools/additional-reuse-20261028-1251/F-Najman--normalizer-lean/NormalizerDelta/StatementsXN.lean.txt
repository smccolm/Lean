module

public import NormalizerDelta.DefsXN
public import NormalizerDelta.ProofsXN

@[expose] public section

/-!
# X(N) additions (2026-10-10): statements (Stage 0, all `sorry`)

The user approved these additions (2026-10-10: "Yes, let's do that!").  They complete the X(N) statements of
§G (`normG_GammaR`, `normG_pmGammaR`, `BG_GammaR_equiv`, `BG_pmGammaR_equiv` in `Statements.lean`), which give
the modular automorphism group of X(N) as SL₂(ℤ/N)/{±1} but not its order.  Definitions: `DefsXN.lean`.

* §O: the order.  [Γ₀(N) : Γ₁(N)] = φ(N), [Γ₁(N) : Γ(N)] = N, hence (with [SL₂(ℤ) : Γ₀(N)] = ψ(N), the proved
  `Gamma0_index`) [SL₂(ℤ) : Γ(N)] = |SL₂(ℤ/N)| = N³ ∏_{p ∣ N} (1 − 1/p²), and |SL₂(ℤ/N)/{±1}| and the order of
  the modular automorphism group of X(N) are N³/2 ∏_{p ∣ N} (1 − 1/p²) for N ≥ 3 (168 for X(7), the Klein
  quartic).  Via X_Δ(M²) ≅ X(M) (`conj_GammaDelta_sq`) this gives the order for X_Δ(M²) with
  Δ = {d ≡ ±1 mod M} (e.g. N = 49: 168).
  Only the modular automorphisms are counted: that all automorphisms of X(M) are modular is not formalized.
  The order formula is stated for all N ≥ 3 (X(N) has genus ≥ 2 only for N ≥ 7).
* §Q: the same group computed in GL₂⁺(ℚ) (as for B₀(N)): the normalizer of Γ(N) in GL₂⁺(ℚ) is SL₂(ℤ)·ℚ^×, and
  modulo Γ(N)·ℚ^× it is Nor_{SL₂(ℝ)}(±Γ(N))/±Γ(N) ≅ SL₂(ℤ/N)/{±1}.

Conventions as before: quotients are taken in SL₂(ℝ) (`BG`); for Γ(N), which does not contain −1 for N ≥ 3,
the modular automorphism group of X(N) (the quotient in PSL₂(ℝ)) is `BG (pmGammaR N)`.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ## §O. The order -/

/-- [Γ₀(N) : Γ₁(N)] = φ(N) (Mathlib's `Gamma0`, `Gamma1` ≤ SL₂(ℤ)). -/
theorem relIndex_Gamma1_Gamma0 (N : ℕ) [NeZero N] :
    (CongruenceSubgroup.Gamma1 N).relIndex (CongruenceSubgroup.Gamma0 N) = N.totient := by apply relIndex_Gamma1_Gamma0' <;> assumption

/-- [Γ₁(N) : Γ(N)] = N. -/
theorem relIndex_Gamma_Gamma1 (N : ℕ) [NeZero N] :
    (CongruenceSubgroup.Gamma N).relIndex (CongruenceSubgroup.Gamma1 N) = N := by apply relIndex_Gamma_Gamma1' <;> assumption

/-- [SL₂(ℤ) : Γ(N)] = N³ ∏_{p ∣ N} (1 − 1/p²). -/
theorem index_Gamma (N : ℕ) [NeZero N] :
    ((CongruenceSubgroup.Gamma N).index : ℚ) = N ^ 3 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by apply index_Gamma' <;> assumption

/-- |SL₂(ℤ/N)| = N³ ∏_{p ∣ N} (1 − 1/p²). -/
theorem card_SL2_ZMod (N : ℕ) [NeZero N] :
    (Nat.card SL(2, ZMod N) : ℚ) = N ^ 3 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by apply card_SL2_ZMod' <;> assumption

/-- [Nor(Γ(N)) : Γ(N)] = |SL₂(ℤ/N)| = N³ ∏_{p ∣ N} (1 − 1/p²), for every N ≥ 1. -/
theorem card_BG_GammaR (N : ℕ) [NeZero N] :
    (Nat.card (BG (GammaR N)) : ℚ) = N ^ 3 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by apply card_BG_GammaR' <;> assumption

/-- |PSL₂(ℤ/N)| = |SL₂(ℤ/N)/{±1}| = N³/2 ∏_{p ∣ N} (1 − 1/p²), for N ≥ 3 (added after the reviews). -/
theorem card_PSL2_ZMod (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    (Nat.card (SL(2, ZMod N) ⧸ pmOneSL N) : ℚ) =
      N ^ 3 / 2 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by apply card_PSL2_ZMod' <;> assumption

/-- **The order of the modular automorphism group of X(N)**: [Nor(±Γ(N)) : ±Γ(N)] = |SL₂(ℤ/N)/{±1}| =
N³/2 ∏_{p ∣ N} (1 − 1/p²), for N ≥ 3. -/
theorem card_BG_pmGammaR (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    (Nat.card (BG (pmGammaR N)) : ℚ) = N ^ 3 / 2 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by apply card_BG_pmGammaR' <;> assumption

/-- For N ≤ 2, −1 ∈ Γ(N) and there is no factor 1/2: the order is 1 (N = 1) or 6 (N = 2). -/
theorem card_BG_pmGammaR_le_two (N : ℕ) [NeZero N] (hN : N ≤ 2) :
    (Nat.card (BG (pmGammaR N)) : ℚ) = N ^ 3 * ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by apply card_BG_pmGammaR_le_two' <;> assumption

/-- Sanity: X(7), the Klein quartic, has 168 modular automorphisms. -/
theorem card_BG_pmGammaR_seven : Nat.card (BG (pmGammaR 7)) = 168 := by apply card_BG_pmGammaR_seven' <;> assumption

/-- The curves X_Δ(M²) with Δ = {d ≡ ±1 mod M}: for M ≥ 3,
[Nor(Γ_Δ(M²)) : Γ_Δ(M²)] = M³/2 ∏_{p ∣ M} (1 − 1/p²) = |PSL₂(ℤ/M)| (X_Δ(M²) ≅ X(M)).  (`3 ≤ M` is needed: for
M = 2, Γ_Δ(4) = Γ₀(4) and the order is 6, not 3.  For M = 3, 4, 6, Δ is all of (ℤ/M²)ˣ and the value is |B(M²)|.)
For example N = 49 (Δ = ⟨−1, 27⟩), 64 (⟨−1, 25, 63⟩), 81 (⟨−1, 8⟩), 100 (⟨−1, 9⟩), 121 (⟨−1, 10⟩),
144 (⟨−1, 11, 71⟩), 169 (⟨−1, 12⟩), 196 (⟨−1, 13⟩).  Other Δ at level M² (e.g. ⟨−1, 19⟩ = {±1 mod 20} at
N = 100, which gives X₁(5, 20)) are not covered. -/
theorem card_BG_GammaDeltaR_sq (M : ℕ) (hM : 3 ≤ M) :
    (Nat.card (BG (GammaDeltaR (M ^ 2) (deltaPm (M ^ 2) M (dvd_pow_self M two_ne_zero)))) : ℚ) =
      M ^ 3 / 2 * ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℚ) ^ 2) := by apply card_BG_GammaDeltaR_sq' <;> assumption

/-- X_Δ(49), Δ = {d ≡ ±1 mod 7}, has 168 modular automorphisms. -/
theorem card_BG_GammaDeltaR_49 :
    Nat.card (BG (GammaDeltaR 49 (deltaPm 49 7 (by norm_num)))) = 168 := by apply card_BG_GammaDeltaR_49' <;> assumption

/-! ## §Q. In GL₂⁺(ℚ) -/

/-- The normalizer of Γ(N) in GL₂⁺(ℚ) is SL₂(ℤ)·ℚ^× (ℚ^× = the centre, `mem_center_GLPos_iff`). -/
theorem normGQ_GammaQ (N : ℕ) [NeZero N] :
    NormGQ (GammaQ N) = SL2ZQ ⊔ Subgroup.center (GLPos (Fin 2) ℚ) := by apply normGQ_GammaQ' <;> assumption

/-- g ↦ (det g)^{-1/2} g maps Nor_{GL₂⁺(ℚ)}(Γ(N)) onto Nor_{SL₂(ℝ)}(±Γ(N))/±Γ(N), with kernel Γ(N)·ℚ^×; the clause
`IsClassOf` pins φ down.  (The target is ±Γ(N), not Γ(N): the scalar −1 maps to −1, which lies in ±Γ(N) but, for
N ≥ 3, not in Γ(N).) -/
theorem BQ_GammaQ_equiv_BG (N : ℕ) [NeZero N] :
    ∃ φ : NormGQ (GammaQ N) →* BG (pmGammaR N), Function.Surjective φ ∧
      φ.ker = (GammaQ N ⊔ Subgroup.center (GLPos (Fin 2) ℚ)).subgroupOf (NormGQ (GammaQ N)) ∧
      ∀ g : NormGQ (GammaQ N), (φ g).IsClassOf (normSL g) := by apply BQ_GammaQ_equiv_BG' <;> assumption

/-- Nor_{GL₂⁺(ℚ)}(Γ(N)) modulo Γ(N)·ℚ^× is SL₂(ℤ/N)/{±1}: the class of γ ∈ SL₂(ℤ) goes to the class of
γ mod N.  (φ is pinned down: it kills ℚ^× by the kernel clause, is fixed on SL₂(ℤ) by the last clause, and
Nor_{GL₂⁺(ℚ)}(Γ(N)) = SL₂(ℤ)·ℚ^× by `normGQ_GammaQ`.) -/
theorem BQ_GammaQ_equiv (N : ℕ) [NeZero N] :
    ∃ φ : NormGQ (GammaQ N) →* SL(2, ZMod N) ⧸ pmOneSL N, Function.Surjective φ ∧
      φ.ker = (GammaQ N ⊔ Subgroup.center (GLPos (Fin 2) ℚ)).subgroupOf (NormGQ (GammaQ N)) ∧
      ∀ (γ : SL(2, ℤ)) (hγ : toGLPosQ γ ∈ NormGQ (GammaQ N)),
        φ ⟨toGLPosQ γ, hγ⟩ = QuotientGroup.mk (redSL N γ) := by apply BQ_GammaQ_equiv' <;> assumption

end

end NormalizerLean
