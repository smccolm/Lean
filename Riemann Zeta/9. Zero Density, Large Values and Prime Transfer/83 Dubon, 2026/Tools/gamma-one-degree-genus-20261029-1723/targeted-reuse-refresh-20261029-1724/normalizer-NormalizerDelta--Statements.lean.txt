module

public import NormalizerDelta.Defs
public import NormalizerDelta.Proofs

@[expose] public section

/-!
# Normalizers of Γ_Δ(N), Γ(N) and ±Γ₁(N): statements (Stage 0, all `sorry`)

Plan: `~/automorphisms_X1/notes/2026-10-08-lean-delta-plan.md`.  The definitions are in `NormalizerDelta/Defs.lean`; the B(N)
definitions (`Gamma0R`, `Norm0`, `IsAtkinLehner`, `IsNewmanForm`, `hPart`, `projSL`, `S`) are those
of `NormalizerLean/Defs.lean`, unchanged.

* §D: basic facts on Γ_Δ(N), the generalized Newman bound, sanity statements.
* §C: Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)) if h_Δ = h(N) (not in general: S₇ at level 49), and
  [Nor(Γ_Δ(N)) : Γ_Δ(N)] = i_Δ · s_Δ, with s_Δ = #{Q ∥ N : ι_Q(Δ) = Δ} if 4 ∤ N, 9 ∤ N.
* §G: Nor(Γ(N)) = SL₂(ℤ), and the modular automorphism group of X(N) is SL₂(ℤ/N)/{±1};
  X_Δ(N) ≅ X₁(M, N/M) for Δ = {±1 mod N/M} (X(M) for N = M²).
* §K: Kim–Koo / Lang: Nor(±Γ₁(N)) = ⟨Γ₀(N), w_Q⟩ for N ≠ 4, its order 2^{ω(N)} φ(N)/2 (N ≥ 3,
  N ≠ 4), and the diamond subgroup is normal with elementary abelian quotient; the exception N = 4.

These statements were reviewed in two rounds on 2026-10-08 (notes in `review/` of the development
repository).

No statement changes after the user's review without the user's approval.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ## §D. Γ_Δ(N) and the generalized Newman bound -/

/-- Γ₀(N) normalizes Γ_Δ(N), for every Δ: the diamond operators act on X_Δ(N). -/
theorem Gamma0R_le_normG_GammaDeltaR (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) :
    Gamma0R N ≤ NormG (GammaDeltaR N Δ) := by apply Gamma0R_le_normG_GammaDeltaR' <;> assumption

/-- [Γ₀(N) : Γ_Δ(N)] = [(ℤ/N)ˣ : Δ] = i_Δ (for −1 ∈ Δ this is the degree of
X_Δ(N) → X₀(N)). -/
theorem relindex_GammaDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    (GammaDelta N Δ).relIndex (CongruenceSubgroup.Gamma0 N) = Δ.index := by apply relindex_GammaDelta' <;> assumption

/-- Sanity: Δ = (ℤ/N)ˣ gives Γ₀(N). -/
theorem GammaDelta_top (N : ℕ) : GammaDelta N ⊤ = CongruenceSubgroup.Gamma0 N := by apply GammaDelta_top' <;> assumption

/-- Sanity: Δ = {±1} gives ±Γ₁(N), with Mathlib's `CongruenceSubgroup.Gamma1`. -/
theorem GammaDelta_pmOne (N : ℕ) :
    GammaDelta N (pmOne N) = CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1) := by apply GammaDelta_pmOne' <;> assumption

/-- Sanity: for Δ = (ℤ/N)ˣ, ε_Δ = gcd(N, 24). -/
theorem epsDelta_top (N : ℕ) [NeZero N] : epsDelta N ⊤ = Nat.gcd N 24 := by apply epsDelta_top' <;> assumption

/-- Sanity: for Δ = {±1}, ε_Δ = N. -/
theorem epsDelta_pmOne (N : ℕ) [NeZero N] : epsDelta N (pmOne N) = N := by apply epsDelta_pmOne' <;> assumption

/-- Sanity: h(N) ∣ h_Δ. -/
theorem hPart_dvd_hDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    hPart N ∣ hDelta N Δ := by apply hPart_dvd_hDelta' <;> assumption

/-- Sanity: h_Δ² ∣ N, so n_Δ = N / h_Δ² is an exact quotient. -/
theorem hDelta_sq_dvd (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    hDelta N Δ ^ 2 ∣ N := by apply hDelta_sq_dvd' <;> assumption

/-- Sanity: for Δ = (ℤ/N)ˣ, h_Δ = h(N). -/
theorem hDelta_top (N : ℕ) [NeZero N] : hDelta N ⊤ = hPart N := by apply hDelta_top' <;> assumption

/-- Sanity: with h = h(N) the form of `newman_delta` is Newman's form (8′). -/
theorem isNewmanFormH_hPart_iff (N : ℕ) (g : SL(2, ℝ)) :
    IsNewmanFormH N (hPart N) g ↔ IsNewmanForm N g := by apply isNewmanFormH_hPart_iff' <;> assumption

/-- **Generalized Newman bound**: every element of the normalizer of Γ_Δ(N) in
SL₂(ℝ) is ±(1/√e)·[[ae, b/h_Δ], [Nc/h_Δ, de]] with a, b, c, d ∈ ℤ, e ∣ n_Δ, ade² − bcn_Δ = e
(which forces e ∥ n_Δ).
For any subgroup Δ, not only for −1 ∈ Δ (note that Nor(Γ_Δ(N)) ≤ Nor(Γ_{±Δ}(N)) and
ε_{±Δ} = ε_Δ). -/
theorem newman_delta {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) {g : SL(2, ℝ)}
    (hg : g ∈ NormG (GammaDeltaR N Δ)) : IsNewmanFormH N (hDelta N Δ) g := by apply newman_delta' <;> assumption

/-- The bound is only a necessary condition: S₂ = [[1, 1/2], [0, 1]] has the form of `newman_delta` for
Δ = {±1}, N = 8 (h_Δ = 2), but does not normalize ±Γ₁(8). -/
theorem newman_delta_not_sufficient :
    IsNewmanFormH 8 (hDelta 8 (pmOne 8)) (S 2) ∧ S 2 ∉ NormG (GammaDeltaR 8 (pmOne 8)) := by apply newman_delta_not_sufficient' <;> assumption

/-! ## §C. Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)), and the index -/

/-- If h_Δ = h(N), then Nor(Γ_Δ(N)) ≤ Nor(Γ₀(N)). -/
theorem normG_GammaDeltaR_le_Norm0 {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ)
    (h : hDelta N Δ = hPart N) : NormG (GammaDeltaR N Δ) ≤ Norm0 N := by apply normG_GammaDeltaR_le_Norm0' <;> assumption

/-- Without h_Δ = h(N) this fails: for N = 49 and
Δ = {d ≡ ±1 mod 7} (h_Δ = 7, h(49) = 1), S₇ = [[1, 1/7], [0, 1]] normalizes Γ_Δ(49) but not Γ₀(49). -/
theorem S7_mem_normG_GammaDeltaR_49 :
    S 7 ∈ NormG (GammaDeltaR 49 (deltaPm 49 7 (by norm_num))) ∧ S 7 ∉ Norm0 49 := by apply S7_mem_normG_GammaDeltaR_49' <;> assumption

/-- **The index**: if h_Δ = h(N), then [Nor(Γ_Δ(N)) : Γ_Δ(N)] = i_Δ · s_Δ, where
i_Δ = [(ℤ/N)ˣ : Δ] and s_Δ is the number of elements of B(N) normalizing Γ_Δ(N).
(For −1 ∈ Δ this is the order of the modular automorphism group of X_Δ(N); the
identity of indices holds for every Δ.) -/
theorem card_BG_GammaDeltaR {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ)
    (h : hDelta N Δ = hPart N) : Nat.card (BG (GammaDeltaR N Δ)) = Δ.index * sDelta N Δ := by apply card_BG_GammaDeltaR' <;> assumption

/-- **The count s_Δ**: if 4 ∤ N and 9 ∤ N, then s_Δ = #{Q ∥ N : ι_Q(Δ) = Δ}, where
ι_Q(d) ≡ d⁻¹ mod Q and ι_Q(d) ≡ d mod N/Q.
Neither h_Δ = h(N) nor −1 ∈ Δ is assumed, on purpose: s_Δ counts elements of B(N) (not of
Nor(Γ_Δ(N))/Γ₀(N)); for 4 ∤ N, 9 ∤ N these are the classes of the w_Q, and
w_Q Γ_Δ(N) w_Q⁻¹ = Γ_{ι_Q(Δ)}(N) for every Δ.  (h_Δ = h(N) is needed only in `card_BG_GammaDeltaR`.) -/
theorem sDelta_eq_sIota {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ) (h4 : ¬ 4 ∣ N) (h9 : ¬ 9 ∣ N) :
    sDelta N Δ = sIota N Δ := by apply sDelta_eq_sIota' <;> assumption

/-- **The index**, combined with `sDelta_eq_sIota`: if h_Δ = h(N), 4 ∤ N and 9 ∤ N, then
[Nor(Γ_Δ(N)) : Γ_Δ(N)] = i_Δ · #{Q ∥ N : ι_Q(Δ) = Δ}. -/
theorem card_BG_GammaDeltaR_of_not_dvd {N : ℕ} [NeZero N] (Δ : Subgroup (ZMod N)ˣ)
    (h : hDelta N Δ = hPart N) (h4 : ¬ 4 ∣ N) (h9 : ¬ 9 ∣ N) :
    Nat.card (BG (GammaDeltaR N Δ)) = Δ.index * sIota N Δ := by apply card_BG_GammaDeltaR_of_not_dvd' <;> assumption

/-! ## §G. Γ(N) and X(N) -/

/-- The normalizer of Γ(N) in SL₂(ℝ) is SL₂(ℤ), for every N ≥ 1. -/
theorem normG_GammaR (N : ℕ) [NeZero N] : NormG (GammaR N) = SL2ZR := by apply normG_GammaR' <;> assumption

/-- The normalizer of ±Γ(N) in SL₂(ℝ) is SL₂(ℤ), for every N ≥ 1. -/
theorem normG_pmGammaR (N : ℕ) [NeZero N] : NormG (pmGammaR N) = SL2ZR := by apply normG_pmGammaR' <;> assumption

/-- Nor(Γ(N))/Γ(N) ≅ SL₂(ℤ/N), the class of γ ∈ SL₂(ℤ) going to γ mod N.  (For N ≥ 3 this is a
double cover of the modular automorphism group of X(N); see `BG_pmGammaR_equiv`.) -/
theorem BG_GammaR_equiv (N : ℕ) [NeZero N] :
    ∃ φ : BG (GammaR N) ≃* SL(2, ZMod N),
      ∀ (γ : SL(2, ℤ)) (x : BG (GammaR N)), x.IsClassOf (ofZ γ) → φ x = redSL N γ := by apply BG_GammaR_equiv' <;> assumption

/-- **The modular automorphism group of X(N)**: Nor(±Γ(N))/±Γ(N) ≅ SL₂(ℤ/N)/{±1}, the class of
γ ∈ SL₂(ℤ) going to the class of γ mod N.  (For N ≤ 2, −1 ∈ Γ(N) and {±1} = 1, so this is the
same as `BG_GammaR_equiv`.) -/
theorem BG_pmGammaR_equiv (N : ℕ) [NeZero N] :
    ∃ φ : BG (pmGammaR N) ≃* SL(2, ZMod N) ⧸ pmOneSL N,
      ∀ (γ : SL(2, ℤ)) (x : BG (pmGammaR N)), x.IsClassOf (ofZ γ) →
        φ x = QuotientGroup.mk (redSL N γ) := by apply BG_pmGammaR_equiv' <;> assumption

/-- The case N = M² of `conj_GammaDelta_X1MN`: for
Δ = {d : d ≡ ±1 mod M}, conjugation by diag(M, 1) maps Γ_Δ(M²) onto ±Γ(M), so X_Δ(M²) ≅ X(M).
(`projSL` rescales diag(M, 1) to diag(√M, 1/√M) ∈ SL₂(ℝ), which conjugates in the same way:
[[a, b], [c, d]] ↦ [[a, Mb], [c/M, d]].  `0 < M` is needed: at M = 0 `projSL` has a junk value.) -/
theorem conj_GammaDelta_sq (M : ℕ) (hM : 0 < M) :
    (GammaDeltaR (M ^ 2) (deltaPm (M ^ 2) M (dvd_pow_self M two_ne_zero))).map
        (MulAut.conj (projSL !![(M : ℝ), 0; 0, 1])).toMonoidHom = pmGammaR M := by apply conj_GammaDelta_sq' <;> assumption

/-- If M² ∣ N and
Δ = {d : d ≡ ±1 mod N/M}, conjugation by diag(M, 1) maps Γ_Δ(N) onto ±(Γ(M) ∩ Γ₁(N/M)), so
X_Δ(N) ≅ X₁(M, N/M).  (For N = M² this is `conj_GammaDelta_sq`, as Γ(M) ∩ Γ₁(M) = Γ(M).) -/
theorem conj_GammaDelta_X1MN {M N : ℕ} [NeZero N] (hM : 0 < M) (hMN : M ^ 2 ∣ N) :
    (GammaDeltaR N (deltaPm N (N / M)
        (Nat.div_dvd_of_dvd ((dvd_pow_self M two_ne_zero).trans hMN)))).map
        (MulAut.conj (projSL !![(M : ℝ), 0; 0, 1])).toMonoidHom =
      toR (CongruenceSubgroup.Gamma M ⊓ CongruenceSubgroup.Gamma1 (N / M)) ⊔
        Subgroup.zpowers (-1) := by apply conj_GammaDelta_X1MN' <;> assumption

/-! ## §K. ±Γ₁(N) and X₁(N) -/

/-- Γ₀(N) normalizes ±Γ₁(N) (the diamond operators), for every N ≥ 1. -/
theorem Gamma0R_le_normG_pmGamma1R (N : ℕ) [NeZero N] : Gamma0R N ≤ NormG (pmGamma1R N) := by apply Gamma0R_le_normG_pmGamma1R' <;> assumption

/-- Every Atkin–Lehner element w_Q (Q ∣ N) normalizes ±Γ₁(N), for every N ≥ 1.
(`hQ` is essential, as for Γ₀(N): see `IsAtkinLehner`.) -/
theorem isAtkinLehner_mem_normG_pmGamma1R {N Q : ℕ} [NeZero N] (hQ : Q ∣ N) {g : SL(2, ℝ)}
    (hg : IsAtkinLehner N Q g) : g ∈ NormG (pmGamma1R N) := by apply isAtkinLehner_mem_normG_pmGamma1R' <;> assumption

/-- **Kim–Koo, Lang**: for N ≠ 4 the normalizer of ±Γ₁(N) in SL₂(ℝ) is generated by Γ₀(N) and
the Atkin–Lehner elements.  Stated as a set: g normalizes ±Γ₁(N) iff g is an Atkin–Lehner element
w_Q for some Q ∥ N (Q = 1 gives Γ₀(N), by `isAtkinLehner_one_iff`).  The condition
`Nat.Coprime Q (N / Q)` is implied by `Q ∣ N` and `IsAtkinLehner N Q g`. -/
theorem normG_pmGamma1R {N : ℕ} [NeZero N] (hN : N ≠ 4) (g : SL(2, ℝ)) :
    g ∈ NormG (pmGamma1R N) ↔
      ∃ Q : ℕ, Q ∣ N ∧ Nat.Coprime Q (N / Q) ∧ IsAtkinLehner N Q g := by apply normG_pmGamma1R' <;> assumption

/-- The case Q = 1 of `normG_pmGamma1R`: the Atkin–Lehner elements for Q = 1 are exactly Γ₀(N). -/
theorem isAtkinLehner_one_iff (N : ℕ) (g : SL(2, ℝ)) : IsAtkinLehner N 1 g ↔ g ∈ Gamma0R N := by apply isAtkinLehner_one_iff' <;> assumption

/-- The exception N = 4: ±Γ₁(4) = Γ₀(4). -/
theorem pmGamma1R_four : pmGamma1R 4 = Gamma0R 4 := by apply pmGamma1R_four' <;> assumption

/-- The exception N = 4: S₂ = [[1, 1/2], [0, 1]] normalizes ±Γ₁(4), but is not an Atkin–Lehner
element of level 4. -/
theorem S2_mem_normG_pmGamma1R_four :
    S 2 ∈ NormG (pmGamma1R 4) ∧ ∀ Q : ℕ, Q ∣ 4 → ¬ IsAtkinLehner 4 Q (S 2) := by apply S2_mem_normG_pmGamma1R_four' <;> assumption

/-- The exception N = 4: |Nor(±Γ₁(4))/±Γ₁(4)| = |B(4)| = 6, not 2^{ω(4)} φ(4)/2 = 2. -/
theorem card_BG_pmGamma1R_four : Nat.card (BG (pmGamma1R 4)) = 6 := by apply card_BG_pmGamma1R_four' <;> assumption

/-- **The order of the modular automorphism group of X₁(N)**:
|Nor(±Γ₁(N))/±Γ₁(N)| = 2^{ω(N)} φ(N)/2 for N ≥ 3, N ≠ 4.  (For N = 1, 2 the ℕ-division φ(N)/2 is 0,
so `3 ≤ N` is needed.) -/
theorem card_BG_pmGamma1R {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) (hN4 : N ≠ 4) :
    Nat.card (BG (pmGamma1R N)) = 2 ^ N.primeFactors.card * (N.totient / 2) := by apply card_BG_pmGamma1R' <;> assumption

/-- The diamond subgroup is normal in Nor(±Γ₁(N))/±Γ₁(N), for every N ≥ 1 (including N = 4,
where it is trivial): every modular automorphism of X₁(N) normalizes the diamond operators. -/
theorem diamonds_normal (N : ℕ) [NeZero N] : (diamonds N).Normal := by apply diamonds_normal' <;> assumption

/-- The diamond subgroup has order φ(N)/2 for N ≥ 3. -/
theorem card_diamonds {N : ℕ} [NeZero N] (hN3 : 3 ≤ N) : Nat.card (diamonds N) = N.totient / 2 := by apply card_diamonds' <;> assumption

/-- For N ≠ 4 the quotient by the diamonds is (ℤ/2)^{ω(N)}, stated as a surjection onto
(ℤ/2)^{primes of N} with kernel the diamond subgroup, which sends the class of w_Q to the indicator
of the primes dividing Q. -/
theorem BG_pmGamma1R_mod_diamonds {N : ℕ} [NeZero N] (hN : N ≠ 4) :
    ∃ σ : BG (pmGamma1R N) →* (N.primeFactors → Multiplicative (ZMod 2)),
      Function.Surjective σ ∧ σ.ker = diamonds N ∧
      ∀ (Q : ℕ) (g : SL(2, ℝ)) (x : BG (pmGamma1R N)), Q ∣ N → IsAtkinLehner N Q g →
        x.IsClassOf g → σ x = fun p : N.primeFactors =>
          if (p : ℕ) ∣ Q then Multiplicative.ofAdd (1 : ZMod 2) else 1 := by apply BG_pmGamma1R_mod_diamonds' <;> assumption

end

end NormalizerLean
