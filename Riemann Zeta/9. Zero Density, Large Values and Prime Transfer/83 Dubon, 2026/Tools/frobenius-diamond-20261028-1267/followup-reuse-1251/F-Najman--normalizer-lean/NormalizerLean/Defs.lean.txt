module

public import Mathlib

@[expose] public section

/-!
# B(N) = Norm_{SL₂(ℝ)}(Γ₀(N)) / Γ₀(N): definitions

The definitions of the handover note `~/automorphisms_X1/notes/2026-10-02-lean-BN-handover.md` (§4).
They were moved verbatim from `Statements.lean` (frozen at commit 11358c3), so that the proof files can
import them and `Statements.lean` can import the proofs.  No definition changes without the user's
approval.  The conventions are explained in `Statements.lean`.

This file holds the definitions of all six parts: those of Parts 2–6 follow, moved verbatim from
`NormalizerDelta/Defs.lean`, `DefsExtra.lean`, `DefsXN.lean`, `DefsCartan.lean` and `DefsGeneral.lean`, which
now only import this file.  They are in one file because the Comparator challenges (`Challenge/*.lean`) copy
them: Lean shares the auxiliary `_proof_n` lemmas of a file between its declarations, so a copy compiles to the
same constants as the library only if it keeps the library's order; each challenge copies whole parts of this
file, in order.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ## Definitions -/

/-- Γ₀(N) as a subgroup of SL₂(ℝ): the image of Mathlib's `CongruenceSubgroup.Gamma0 N ≤ SL(2, ℤ)`. -/
def Gamma0R (N : ℕ) : Subgroup SL(2, ℝ) :=
  (CongruenceSubgroup.Gamma0 N).map (SpecialLinearGroup.map (Int.castRingHom ℝ))

/-- The normalizer of Γ₀(N) in SL₂(ℝ). -/
abbrev Norm0 (N : ℕ) : Subgroup SL(2, ℝ) :=
  Subgroup.normalizer (Gamma0R N : Set SL(2, ℝ))

/-- **B(N) = Norm_{SL₂(ℝ)}(Γ₀(N)) / Γ₀(N).** -/
abbrev B (N : ℕ) : Type :=
  Norm0 N ⧸ (Gamma0R N).subgroupOf (Norm0 N)

instance (N : ℕ) : ((Gamma0R N).subgroupOf (Norm0 N)).Normal :=
  Subgroup.normal_in_normalizer

/-- `x : B N` is the class of the real matrix `g`: `g` normalizes Γ₀(N) and `x = g Γ₀(N)`. -/
def B.IsClassOf {N : ℕ} (x : B N) (g : SL(2, ℝ)) : Prop :=
  ∃ hg : g ∈ Norm0 N, x = QuotientGroup.mk ⟨g, hg⟩

/-- The image in SL₂(ℝ) of a real 2×2 matrix `A` of positive determinant: `(det A)^{-1/2} • A`.
Junk value `1` if `det A ≤ 0`; below it is only applied to matrices of positive determinant. -/
def projSL (A : Matrix (Fin 2) (Fin 2) ℝ) : SL(2, ℝ) :=
  if hA : 0 < A.det then
    ⟨(Real.sqrt A.det)⁻¹ • A, by
      rw [det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt hA.le, inv_mul_cancel₀ hA.ne']⟩
  else 1

/-- h(N) = 2^{min(3, ⌊v₂(N)/2⌋)} · 3^{min(1, ⌊v₃(N)/2⌋)}.  By `hPart_isGreatest` this is the largest
divisor of 24 whose square divides N. -/
def hPart (N : ℕ) : ℕ :=
  2 ^ min 3 (N.factorization 2 / 2) * 3 ^ min 1 (N.factorization 3 / 2)

/-- n(N) = N / h(N)². -/
def nPart (N : ℕ) : ℕ := N / hPart N ^ 2

/-- m_p = p^{v_p(N)}, the exact power of `p` dividing `N`. -/
def mPart (N p : ℕ) : ℕ := p ^ N.factorization p

/-- ψ(t) = t ∏_{p ∣ t} (1 + 1/p).  By `Gamma0_index` this is μ(t) = [SL₂(ℤ) : Γ₀(t)]. -/
def psi (t : ℕ) : ℚ := t * ∏ p ∈ t.primeFactors, (1 + 1 / (p : ℚ))

/-- S_k = [[1, 1/k], [0, 1]]. -/
def S (k : ℕ) : SL(2, ℝ) :=
  ⟨!![1, (k : ℝ)⁻¹; 0, 1], by simp [det_fin_two]⟩

/-- `g` is an Atkin–Lehner element w_Q of level N:
`g = (1/√Q)·[[Qx, y], [Nz, Qw]]` with `x y z w : ℤ` and `Q²xw − Nyz = Q`.
No divisibility is built in: the theorems below add the hypothesis `Q ∣ N`, which then forces
Q ∥ N.  That hypothesis is essential: for N = 4, Q = 8 the element (1/√8)·[[0, 1], [−8, 0]]
satisfies the equation but does not normalize Γ₀(4).  For Q = 0 the predicate is false. -/
def IsAtkinLehner (N Q : ℕ) (g : SL(2, ℝ)) : Prop :=
  ∃ x y z w : ℤ, (Q : ℤ) ^ 2 * x * w - N * y * z = Q ∧
    (g : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt Q)⁻¹ • !![(Q : ℝ) * x, (y : ℝ); (N : ℝ) * z, (Q : ℝ) * w]

/-- `x : B N` is the class w_Q: an Atkin–Lehner element for `Q` exists, and every one represents `x`. -/
def B.IsALClass {N : ℕ} (x : B N) (Q : ℕ) : Prop :=
  (∃ g, IsAtkinLehner N Q g) ∧ ∀ g, IsAtkinLehner N Q g → x.IsClassOf g

/-- `g` has Newman's form (8′) [Nw, Theorem]:
`g = ±(1/√e)·[[ae, b/h], [Nc/h, de]]` with `a b c d : ℤ`, `e ≥ 1`, `e ∣ n`, `ade² − bcn = e`. -/
def IsNewmanForm (N : ℕ) (g : SL(2, ℝ)) : Prop :=
  ∃ (a b c d : ℤ) (e : ℕ), 0 < e ∧ e ∣ nPart N ∧
    a * d * (e : ℤ) ^ 2 - b * c * (nPart N : ℤ) = e ∧
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) =
        (ε / Real.sqrt e) •
          !![(a : ℝ) * e, (b : ℝ) / hPart N; (N : ℝ) * c / hPart N, (d : ℝ) * e]

/-- D = diag(h, 1), rescaled into SL₂(ℝ): `diag(√h, 1/√h)`.  Conjugation by it equals conjugation by D. -/
def Dsl (N : ℕ) : SL(2, ℝ) := projSL !![(hPart N : ℝ), 0; 0, 1]

/-- D⁻¹ Γ₀(n) D ≤ SL₂(ℝ). -/
def conjGamma0n (N : ℕ) : Subgroup SL(2, ℝ) :=
  (Gamma0R (nPart N)).map (MulAut.conj (Dsl N)⁻¹).toMonoidHom

/-- C(N) = D⁻¹ Γ₀(n) D / Γ₀(N), as a subgroup of B(N): by definition the image in B(N) of
D⁻¹ Γ₀(n) D ∩ Norm(Γ₀(N)).  By `conjGamma0n_le_normalizer` the intersection is all of D⁻¹ Γ₀(n) D. -/
def CN (N : ℕ) : Subgroup (B N) :=
  ((conjGamma0n N).subgroupOf (Norm0 N)).map
    (QuotientGroup.mk' ((Gamma0R N).subgroupOf (Norm0 N)))

/-- The classes of w_{m_p} and S_{h(m_p)} in B(N): the set of `x` that are the class w_{m_p}
(`B.IsALClass`) or the class of S_{h(m_p)}.  That both classes exist is part of T1
(`exists_isAtkinLehner`, `isAtkinLehner_mem_normalizer`, `isAtkinLehner_mul_inv_mem`,
`S_mem_normalizer`); if one did not, this set would be smaller and T4–T7 would become harder,
not weaker. -/
def localGens (N p : ℕ) : Set (B N) :=
  {x | x.IsALClass (mPart N p) ∨ x.IsClassOf (S (hPart (mPart N p)))}

/-- The local subgroup B_p = ⟨w_{m_p}, S_{h(m_p)}⟩ ≤ B(N). -/
def Bloc (N p : ℕ) : Subgroup (B N) := Subgroup.closure (localGens N p)

/-- f₂(a) = |B(2ᵃ)|: 1, 2, 6, 8, 24, 32, 96, 128 for a = 0, …, 6, ≥ 7. -/
def f₂ : ℕ → ℕ
  | 0 => 1 | 1 => 2 | 2 => 6 | 3 => 8 | 4 => 24 | 5 => 32 | 6 => 96 | _ => 128

/-- f₃(b) = |B(3ᵇ)|: 1, 2, 12, 18 for b = 0, 1, 2, ≥ 3. -/
def f₃ : ℕ → ℕ
  | 0 => 1 | 1 => 2 | 2 => 12 | _ => 18

/-! ### Presentations -/

/-- The two generators of a local presentation. -/
inductive LGen
  | w
  | s
  deriving DecidableEq

/-- `[x, y] = x⁻¹ y⁻¹ x y` (blueprint convention, not Mathlib's `⁅x, y⁆`). -/
def bracket {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

namespace Words

/-- The word `w`. -/
abbrev w : FreeGroup LGen := FreeGroup.of .w
/-- The word `s`. -/
abbrev s : FreeGroup LGen := FreeGroup.of .s
/-- `r = w s⁻¹ w`, an abbreviation, not a generator [BA]. -/
abbrev r : FreeGroup LGen := w * s⁻¹ * w

end Words

open Words in
/-- The relations of [BA] beyond `w² = sʰ = 1`, for the prime power `pᵃ`:
* 4, 9, 16: (ws)³ = 1;
* 8, 2ᵃ (a ≥ 9), 3ᵇ (b ≥ 3): [r, s] = 1;
* 32, 64, 128, 256: relations (4), (5), (6), (7) of [BA];
* otherwise (h = 1): nothing.
(A `List`, so that the relators can be evaluated numerically as a sanity check.) -/
def localExtraRels : ℕ → ℕ → List (FreeGroup LGen)
  | 2, 2 | 2, 4 | 3, 2 => [(w * s) ^ 3]
  | 2, 3 => [bracket r s]
  -- (4), m = 32
  | 2, 5 => [bracket (r ^ 2) s, bracket (s ^ 2) r, bracket r s * (r ^ 2 * s ^ 2)⁻¹]
  -- (5), m = 64, with u = s⁴, v = w s⁴ w
  | 2, 6 =>
    let u := s ^ 4
    let v := w * s ^ 4 * w
    [(w * s) ^ 3, bracket u v, s * v * s⁻¹ * (u * v)⁻¹]
  -- (6), m = 128
  | 2, 7 => [bracket (r ^ 2) (s ^ 2), r⁻¹ * s ^ 2 * r * (r ^ 4 * s ^ 2)⁻¹,
      s⁻¹ * r ^ 2 * s * (r ^ 2 * s ^ 4)⁻¹, bracket r s * (r ^ 6 * s ^ 2)⁻¹]
  -- (7), m = 256
  | 2, 8 => [bracket (r ^ 2) s, r⁻¹ * s * r * (r ^ 4 * s ^ 5)⁻¹]
  | 2, a => if 9 ≤ a then [bracket r s] else []
  | 3, b => if 3 ≤ b then [bracket r s] else []
  | _, _ => []

/-- The relators of the local presentation of B(pᵃ): `w²`, `s^{h(pᵃ)}` and `localExtraRels p a`. -/
def localRelList (p a : ℕ) : List (FreeGroup LGen) :=
  [Words.w ^ 2, Words.s ^ hPart (p ^ a)] ++ localExtraRels p a

/-- The local presentation of B(pᵃ), as a set of relators. -/
def localRels (p a : ℕ) : Set (FreeGroup LGen) := {ρ | ρ ∈ localRelList p a}

/-- Generators of the global presentation: `(p, w)` and `(p, s)` for each prime `p ∣ N`. -/
abbrev GGen (N : ℕ) : Type := N.primeFactors × LGen

/-- The global presentation of B(N) [BA, (1)]: the local relations for each p ∣ N, and for p ≠ q
`[w_p, w_q] = [s_p, s_q] = 1`, `w_p s_q w_p⁻¹ = s_q^{m_p}`. -/
def globalRels (N : ℕ) : Set (FreeGroup (GGen N)) :=
  (⋃ p : N.primeFactors,
      FreeGroup.map (fun x : LGen => (p, x)) '' localRels p (N.factorization p)) ∪
    ⋃ (p : N.primeFactors) (q : N.primeFactors) (_ : p ≠ q),
      {bracket (FreeGroup.of (p, .w)) (FreeGroup.of (q, .w)),
        bracket (FreeGroup.of (p, .s)) (FreeGroup.of (q, .s)),
        FreeGroup.of (p, .w) * FreeGroup.of (q, .s) * (FreeGroup.of (p, .w))⁻¹ *
          (FreeGroup.of (q, .s) ^ mPart N p)⁻¹}

open Words in
/-- Bars's local presentation ⟨w, s | w², sʰ, (ws)ᵏ⟩ (Bars 2008, Prop. 13(2) / Thm 16). -/
def barsRels (h k : ℕ) : Set (FreeGroup LGen) := {w ^ 2, s ^ h, (w * s) ^ k}

/-- w₂₅₆ = [[0, −1/16], [16, 0]]. -/
def w256 : SL(2, ℝ) :=
  ⟨!![0, -1 / 16; 16, 0], by norm_num [det_fin_two]⟩


end

end NormalizerLean

-- Part 2, moved verbatim from `NormalizerDelta/Defs.lean`.

/-!
# Normalizers of Γ_Δ(N), Γ(N) and ±Γ₁(N): definitions

Definitions for the second project in `~/normalizer_lean` (plan:
`~/automorphisms_X1/notes/2026-10-08-lean-delta-plan.md`).  The B(N) definitions of
`NormalizerLean/Defs.lean` (`Gamma0R`, `IsAtkinLehner`, `projSL`, `hPart`, …) are reused unchanged.

Conventions (as for B(N)).
* Every quotient is the honest one: Nor_{SL₂(ℝ)}(Γ) / Γ for a subgroup Γ ≤ SL₂(ℝ) (`BG`).
* Modular automorphism groups are quotients in PSL₂(ℝ).  For a group Γ ∋ −1 the
  SL₂(ℝ)-quotient is the same group; for Γ(N) and Γ₁(N), which do not contain −1 when N ≥ 3, the
  modular automorphism group of the curve is the quotient for ±Γ (`pmGammaR`, `pmGamma1R`).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ## Normalizer quotients -/

/-- The image in SL₂(ℝ) of a subgroup of SL₂(ℤ). -/
def toR (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℝ) :=
  Γ.map (SpecialLinearGroup.map (Int.castRingHom ℝ))

/-- The normalizer of Γ in SL₂(ℝ). -/
abbrev NormG (Γ : Subgroup SL(2, ℝ)) : Subgroup SL(2, ℝ) :=
  Subgroup.normalizer (Γ : Set SL(2, ℝ))

/-- **Nor_{SL₂(ℝ)}(Γ) / Γ.** -/
abbrev BG (Γ : Subgroup SL(2, ℝ)) : Type :=
  NormG Γ ⧸ Γ.subgroupOf (NormG Γ)

instance (Γ : Subgroup SL(2, ℝ)) : (Γ.subgroupOf (NormG Γ)).Normal :=
  Subgroup.normal_in_normalizer

/-- `x : BG Γ` is the class of the real matrix `g`: `g` normalizes Γ and `x = g Γ`. -/
def BG.IsClassOf {Γ : Subgroup SL(2, ℝ)} (x : BG Γ) (g : SL(2, ℝ)) : Prop :=
  ∃ hg : g ∈ NormG Γ, x = QuotientGroup.mk ⟨g, hg⟩

/-! ## Γ_Δ(N) -/

/-- Γ_Δ(N) = {γ ∈ Γ₀(N) : γ₁₁ mod N ∈ Δ} ≤ SL₂(ℤ), for a subgroup Δ ≤ (ℤ/N)ˣ.
(`γ 1 1` is the lower right entry.  For γ ∈ Γ₀(N) it is a unit mod N, since det γ = 1.) -/
def GammaDelta (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ CongruenceSubgroup.Gamma0 N ∧
    ∃ u ∈ Δ, (u : ZMod N) = ((γ 1 1 : ℤ) : ZMod N)}
  one_mem' := ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro γ γ' ⟨h0, u, hu, hγ⟩ ⟨h0', u', hu', hγ'⟩
    refine ⟨Subgroup.mul_mem _ h0 h0', u * u', Subgroup.mul_mem _ hu hu', ?_⟩
    have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 h0
    have e : ((γ * γ') 1 1 : ℤ) = γ 1 0 * γ' 0 1 + γ 1 1 * γ' 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Units.val_mul, hγ, hγ', e]
    push_cast
    rw [hc, zero_mul, zero_add]
  inv_mem' := by
    rintro γ ⟨h0, u, hu, hγ⟩
    refine ⟨Subgroup.inv_mem _ h0, u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
    have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 h0
    have hdet : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have h := congrArg (fun x : ℤ => (x : ZMod N)) γ.2
      simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at h
      rw [hc, mul_zero, sub_zero] at h
      exact h
    have e : (γ⁻¹ 1 1 : ℤ) = γ 0 0 := by
      simp [Matrix.adjugate_fin_two]
    rw [e]
    rw [← hγ] at hdet
    exact Units.inv_eq_of_mul_eq_one_left hdet

/-- Γ_Δ(N) in SL₂(ℝ). -/
def GammaDeltaR (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : Subgroup SL(2, ℝ) := toR (GammaDelta N Δ)

/-- ε_Δ = gcd(N, d² − 1 : d ∈ Δ), with d running over the representatives
`(d : ZMod N).val ∈ [0, N)`.  The truncated subtraction is harmless: for N ≥ 2 a unit has
`val ≥ 1`, and for N = 1 the result is gcd(1, ·) = 1 anyway. -/
def epsDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  haveI := Classical.decPred (· ∈ Δ)
  Nat.gcd N ((Finset.univ.filter (· ∈ Δ)).gcd fun d : (ZMod N)ˣ => (d : ZMod N).val ^ 2 - 1)

/-- h_Δ = ∏_{p ∣ N} p^{min(v_p(ε_Δ), ⌊v_p(N)/2⌋)}. -/
def hDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  ∏ p ∈ N.primeFactors, p ^ min ((epsDelta N Δ).factorization p) (N.factorization p / 2)

/-- `g` has the form of the generalized Newman bound, with parameter h (and n = N/h²):
`g = ±(1/√e)·[[ae, b/h], [Nc/h, de]]` with `a b c d : ℤ`, `e ≥ 1`, `e ∣ n`, `ade² − bcn = e`.
(Together with e ∣ n, the equation forces e ∥ n.  The sign ± is there because we work in SL₂(ℝ).)
For h = h(N) this is `IsNewmanForm N`.  The statements only use h = h(N) or h = h_Δ, which are ≥ 1
with h² ∣ N, so the divisions by h and the ℕ-division N / h² are exact. -/
def IsNewmanFormH (N h : ℕ) (g : SL(2, ℝ)) : Prop :=
  ∃ (a b c d : ℤ) (e : ℕ), 0 < e ∧ e ∣ N / h ^ 2 ∧
    a * d * (e : ℤ) ^ 2 - b * c * ((N / h ^ 2 : ℕ) : ℤ) = e ∧
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) =
        (ε / Real.sqrt e) •
          !![(a : ℝ) * e, (b : ℝ) / h; (N : ℝ) * c / h, (d : ℝ) * e]

/-! ## s_Δ and ι_Q -/

/-- s_Δ: the number of elements of B(N) = Nor(Γ₀(N))/Γ₀(N) that normalize Γ_Δ(N),
i.e. that have a representative normalizing Γ_Δ(N).  (Since Γ₀(N) normalizes Γ_Δ(N), one
representative does iff all do.) -/
def sDelta (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  Nat.card {x : B N // ∃ g : SL(2, ℝ), x.IsClassOf g ∧ g ∈ NormG (GammaDeltaR N Δ)}

/-- `u = ι_Q(d)`: u ≡ d⁻¹ mod Q and u ≡ d mod N/Q.  The reductions are `ZMod.cast`
(for N ≥ 1: take the representative in [0, N) and reduce), which for Q ∣ N are the reduction
maps. -/
def IsIota (N Q : ℕ) (d u : (ZMod N)ˣ) : Prop :=
  (ZMod.cast (u : ZMod N) : ZMod Q) * (ZMod.cast (d : ZMod N) : ZMod Q) = 1 ∧
    (ZMod.cast (u : ZMod N) : ZMod (N / Q)) = (ZMod.cast (d : ZMod N) : ZMod (N / Q))

/-- #{Q ∥ N : ι_Q(Δ) = Δ}, where ι_Q(Δ) = Δ is spelled out as
`u ∈ Δ ↔ u = ι_Q(d)` for some `d ∈ Δ`. -/
def sIota (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  Nat.card {Q : ℕ // Q ∣ N ∧ Nat.Coprime Q (N / Q) ∧ ∀ u, u ∈ Δ ↔ ∃ d ∈ Δ, IsIota N Q d u}

/-! ## Γ(N) and SL₂(ℤ) -/

/-- SL₂(ℤ) as a subgroup of SL₂(ℝ). -/
def SL2ZR : Subgroup SL(2, ℝ) := toR ⊤

/-- Γ(N) in SL₂(ℝ) (Mathlib's `CongruenceSubgroup.Gamma N`: γ ≡ 1 mod N). -/
def GammaR (N : ℕ) : Subgroup SL(2, ℝ) := toR (CongruenceSubgroup.Gamma N)

/-- ±Γ(N) = ⟨Γ(N), −1⟩ in SL₂(ℝ). -/
def pmGammaR (N : ℕ) : Subgroup SL(2, ℝ) := GammaR N ⊔ Subgroup.zpowers (-1)

/-- {±1} ≤ SL₂(ℤ/N) (trivial for N ≤ 2, where −1 = 1). -/
def pmOneSL (N : ℕ) : Subgroup SL(2, ZMod N) := Subgroup.zpowers (-1)

instance (N : ℕ) : (pmOneSL N).Normal where
  conj_mem n hn g := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : g * (-1 : SL(2, ZMod N)) = -1 * g := by rw [mul_neg, neg_mul, mul_one, one_mul]
    rw [(Commute.zpow_right hc k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

/-- Reduction mod N, SL₂(ℤ) → SL₂(ℤ/N). -/
abbrev redSL (N : ℕ) : SL(2, ℤ) →* SL(2, ZMod N) := SpecialLinearGroup.map (Int.castRingHom (ZMod N))

/-- The image in SL₂(ℝ) of an integer matrix. -/
abbrev ofZ (γ : SL(2, ℤ)) : SL(2, ℝ) := SpecialLinearGroup.map (Int.castRingHom ℝ) γ

/-- Δ = {d mod N : d ≡ ±1 mod M} ≤ (ℤ/N)ˣ, for M ∣ N. -/
def deltaPm (N M : ℕ) (hM : M ∣ N) : Subgroup (ZMod N)ˣ :=
  (Subgroup.zpowers (-1 : (ZMod M)ˣ)).comap (Units.map (ZMod.castHom hM (ZMod M)).toMonoidHom)

/-! ## ±Γ₁(N) -/

/-- Δ = {±1} ≤ (ℤ/N)ˣ (trivial for N ≤ 2, where −1 = 1). -/
def pmOne (N : ℕ) : Subgroup (ZMod N)ˣ := Subgroup.zpowers (-1)

/-- ±Γ₁(N) = Γ_{±1}(N) in SL₂(ℝ). -/
def pmGamma1R (N : ℕ) : Subgroup SL(2, ℝ) := GammaDeltaR N (pmOne N)

/-- The diamond subgroup of Nor(±Γ₁(N))/±Γ₁(N): the image of Γ₀(N) ∩ Nor(±Γ₁(N)).
(By `Gamma0R_le_normG_pmGamma1R` this intersection is all of Γ₀(N).) -/
def diamonds (N : ℕ) : Subgroup (BG (pmGamma1R N)) :=
  ((Gamma0R N).subgroupOf (NormG (pmGamma1R N))).map
    (QuotientGroup.mk' ((pmGamma1R N).subgroupOf (NormG (pmGamma1R N))))

end

end NormalizerLean

-- Part 3, moved verbatim from `NormalizerDelta/DefsExtra.lean`.

/-!
# Additions (2026-10-09): M_Δ, the σH coset description, the cases i)–iii), and B₀(N)

Definitions for the statements in `StatementsExtra.lean` (the user approved these additions).
`NormalizerDelta/Defs.lean` and the 34 statements of `Statements.lean` are unchanged.

* M_Δ = D⁻¹ Γ₀(n_Δ)⁺ D, with D = diag(h_Δ, 1) and Γ₀(n)⁺ the subgroup generated
  by all Atkin–Lehner elements of level n (Q = 1 gives Γ₀(n)).
* The coset description used by `aut_orders.py`: representatives σ of Γ₀(N)\SL₂(ℤ) and Hermite forms
  H = [[a, b], [0, d]], a d ∣ N, 0 ≤ b < d, gcd(a, b, d) = 1.
* B₀(N) of the sporadic-points paper (Derickx–Najman, `2511.09015`, §3): there
  B₀(N) := Norm_{GL₂⁺(ℚ)}(Γ₀(N))/Γ₀(N).  Read literally this quotient is infinite (it contains the
  scalars); the intended group is the quotient by Γ₀(N)·ℚ^×.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ## M_Δ -/

/-- Γ₀(n)⁺ ≤ SL₂(ℝ): the subgroup generated by the Atkin–Lehner elements w_Q of level n, Q ∣ n
(for Q = 1 these are the elements of Γ₀(n)). -/
def Gamma0Plus (n : ℕ) : Subgroup SL(2, ℝ) :=
  Subgroup.closure {g | ∃ Q : ℕ, Q ∣ n ∧ IsAtkinLehner n Q g}

/-- n_Δ = N / h_Δ². -/
def nDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : ℕ := N / hDelta N Δ ^ 2

/-- M_Δ = D⁻¹ Γ₀(n_Δ)⁺ D, D = diag(h_Δ, 1) (rescaled into SL₂(ℝ) by `projSL`). -/
def MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : Subgroup SL(2, ℝ) :=
  (Gamma0Plus (nDelta N Δ)).map
    (MulAut.conj (projSL !![(hDelta N Δ : ℝ), 0; 0, 1])⁻¹).toMonoidHom

/-! ## The σH coset description -/

/-- `R` is a set of representatives of the right cosets Γ₀(N)σ of SL₂(ℤ). -/
def IsGamma0Reps (N : ℕ) (R : Set SL(2, ℤ)) : Prop :=
  ∀ σ : SL(2, ℤ), ∃! r : SL(2, ℤ), r ∈ R ∧ σ * r⁻¹ ∈ CongruenceSubgroup.Gamma0 N

/-- H = [[a, b], [0, d]] is one of the Hermite forms of `aut_orders.py`: a, d ≥ 1, a d ∣ N, 0 ≤ b < d,
gcd(a, b, d) = 1. -/
def IsHermiteN (N a b d : ℕ) : Prop :=
  0 < a ∧ 0 < d ∧ a * d ∣ N ∧ b < d ∧ Nat.gcd (Nat.gcd a b) d = 1

/-- The real matrix [[a, b], [0, d]]. -/
def hermMat (a b d : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := !![(a : ℝ), b; 0, d]

/-! ## The cases i)–iii) of `hDelta_eq_hPart_iff` -/

/-- d ≡ ±1 (mod m), for a unit d mod N (reduction by `ZMod.cast`; used with m ∣ N). -/
def IsPmOneMod {N : ℕ} (m : ℕ) (d : (ZMod N)ˣ) : Prop :=
  (ZMod.cast (d : ZMod N) : ZMod m) = 1 ∨ (ZMod.cast (d : ZMod N) : ZMod m) = -1

/-! ## B₀(N) -/

/-- SL₂(ℤ) → GL₂⁺(ℚ). -/
abbrev toGLPosQ : SL(2, ℤ) →* GLPos (Fin 2) ℚ :=
  SpecialLinearGroup.toGLPos.comp (SpecialLinearGroup.map (Int.castRingHom ℚ))

/-- Γ₀(N) in GL₂⁺(ℚ). -/
def Gamma0Q (N : ℕ) : Subgroup (GLPos (Fin 2) ℚ) := (CongruenceSubgroup.Gamma0 N).map toGLPosQ

/-- The normalizer of Γ₀(N) in GL₂⁺(ℚ). -/
abbrev Norm0Q (N : ℕ) : Subgroup (GLPos (Fin 2) ℚ) := Subgroup.normalizer (Gamma0Q N : Set (GLPos (Fin 2) ℚ))

instance (N : ℕ) : ((Gamma0Q N).subgroupOf (Norm0Q N)).Normal := Subgroup.normal_in_normalizer

/-- The literal quotient Norm_{GL₂⁺(ℚ)}(Γ₀(N))/Γ₀(N) of the sporadic-points paper. -/
abbrev B0lit (N : ℕ) : Type := Norm0Q N ⧸ (Gamma0Q N).subgroupOf (Norm0Q N)

/-- The image in SL₂(ℝ) of g ∈ GL₂⁺(ℚ): (det g)^{-1/2} · g. -/
def normSL (g : GLPos (Fin 2) ℚ) : SL(2, ℝ) :=
  projSL (((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.cast : ℚ → ℝ))

end

end NormalizerLean

-- Part 4, moved verbatim from `NormalizerDelta/DefsXN.lean`.

/-!
# X(N) additions (2026-10-10): definitions

Definitions for `StatementsXN.lean`: Γ(N), SL₂(ℤ) and normalizers inside GL₂⁺(ℚ), for the GL₂⁺(ℚ) form of the
modular automorphism group of X(N) (as for B₀(N) in `DefsExtra.lean`).  `NormalizerDelta/Defs.lean`,
`DefsExtra.lean` and all earlier statements are unchanged.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- Γ(N) in GL₂⁺(ℚ). -/
def GammaQ (N : ℕ) : Subgroup (GLPos (Fin 2) ℚ) := (CongruenceSubgroup.Gamma N).map toGLPosQ

/-- SL₂(ℤ) in GL₂⁺(ℚ). -/
def SL2ZQ : Subgroup (GLPos (Fin 2) ℚ) := (⊤ : Subgroup SL(2, ℤ)).map toGLPosQ

/-- The normalizer of a subgroup of GL₂⁺(ℚ). -/
abbrev NormGQ (Γ : Subgroup (GLPos (Fin 2) ℚ)) : Subgroup (GLPos (Fin 2) ℚ) :=
  Subgroup.normalizer (Γ : Set (GLPos (Fin 2) ℚ))

end

end NormalizerLean

-- Part 5, moved verbatim from `NormalizerDelta/DefsCartan.lean`.

/-!
# Cartan modular curves (2026-10-10): definitions

The groups Γ_H = {γ ∈ SL₂(ℤ) : γ mod N ∈ H} (they depend only on H ∩ SL₂(ℤ/N)) of the split and non-split Cartan
subgroups H and of their normalizers, defined by congruence conditions on the entries of γ = [[a, b], [c, d]]:
* Γ_sp(N): γ ≡ [[*, 0], [0, *]] mod N (C_sp = diagonal matrices);
* Γ_sp⁺(N): γ ≡ [[*, 0], [0, *]] or [[0, *], [*, 0]] mod N (diagonal or antidiagonal; for N = p an odd prime this is
  the normalizer C_sp⁺(p) of C_sp(p); for composite N it is in general a proper subgroup of the normalizer, and the
  statements use it only at prime level);
* Γ_ns(N, ε): γ ≡ [[a, εc], [c, a]] mod N (C_ns = {[[x, εy], [y, x]]}, the non-split Cartan subgroup when N = p is
  an odd prime and ε is not a square mod p, i.e. F_p[√ε]^× in the basis 1, √ε);
* Γ_ns⁺(N, ε): γ ≡ [[a, εc], [c, a]] or [[a, −εc], [c, −a]] mod N (C_ns⁺ = C_ns ∪ C_ns·diag(1, −1)).
Different non-squares ε give SL₂(ℤ)-conjugate groups.  Convention: Dose–Lido–Mercuri (arXiv:2005.09009) define Γ_H
with a transpose, so their Γ_{C_ns(ξ)} is `GammaNs p ξ⁻¹` here.
The curves are X_sp(N), X_sp⁺(N), X_ns(p), X_ns⁺(p); as before their modular automorphism groups are
`BG (toR Γ)` (all four groups contain −1).  `NormalizerDelta/Defs.lean` and all earlier statements are unchanged.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- The entries of γ⁻¹ = adj γ for γ ∈ SL₂(ℤ). -/
theorem SL2Z_inv_apply (γ : SL(2, ℤ)) :
    (γ⁻¹ : SL(2, ℤ)) 0 0 = γ 1 1 ∧ (γ⁻¹ : SL(2, ℤ)) 0 1 = -γ 0 1 ∧ (γ⁻¹ : SL(2, ℤ)) 1 0 = -γ 1 0 ∧
      (γ⁻¹ : SL(2, ℤ)) 1 1 = γ 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]

/-- Γ_sp(N) = {γ ∈ SL₂(ℤ) : γ ≡ diagonal mod N}. -/
def GammaSp (N : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {γ | ((γ 0 1 : ℤ) : ZMod N) = 0 ∧ ((γ 1 0 : ℤ) : ZMod N) = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro γ γ' ⟨hb, hc⟩ ⟨hb', hc'⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Int.cast_add, Int.cast_mul, hb, hc, hb', hc', mul_zero, zero_mul, add_zero,
      zero_add, and_self]
  inv_mem' := by
    rintro γ ⟨hb, hc⟩
    simp [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, hb, hc]

/-- Γ_sp⁺(N) = {γ ∈ SL₂(ℤ) : γ ≡ diagonal or antidiagonal mod N} (the normalizer of the split Cartan for N an odd
prime). -/
def GammaSpPlus (N : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {γ | (((γ 0 1 : ℤ) : ZMod N) = 0 ∧ ((γ 1 0 : ℤ) : ZMod N) = 0) ∨
    (((γ 0 0 : ℤ) : ZMod N) = 0 ∧ ((γ 1 1 : ℤ) : ZMod N) = 0)}
  one_mem' := Or.inl (by simp)
  mul_mem' := by
    rintro γ γ' (⟨hb, hc⟩ | ⟨ha, hd⟩) (⟨hb', hc'⟩ | ⟨ha', hd'⟩)
    · left
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
        Int.cast_mul, hb, hc, hb', hc', mul_zero, zero_mul, add_zero, and_self]
    · right
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
        Int.cast_mul, hb, hc, ha', hd', mul_zero, zero_mul, add_zero, and_self]
    · right
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
        Int.cast_mul, ha, hd, hb', hc', mul_zero, zero_mul, add_zero, and_self]
    · left
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
        Int.cast_mul, ha, hd, ha', hd', mul_zero, zero_mul, add_zero, and_self]
  inv_mem' := by
    rintro γ (⟨hb, hc⟩ | ⟨ha, hd⟩)
    · exact Or.inl (by simp [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, hb, hc])
    · exact Or.inr (by simp [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, ha, hd])

/-- Γ_ns(N, ε) = {γ ∈ SL₂(ℤ) : γ ≡ [[a, εc], [c, a]] mod N}. -/
def GammaNs (N : ℕ) (ε : ZMod N) : Subgroup SL(2, ℤ) where
  carrier := {γ | ((γ 1 1 : ℤ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N) ∧
    ((γ 0 1 : ℤ) : ZMod N) = ε * ((γ 1 0 : ℤ) : ZMod N)}
  one_mem' := by simp
  mul_mem' := by
    rintro γ γ' ⟨hd, hb⟩ ⟨hd', hb'⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Int.cast_add, Int.cast_mul, hd, hb, hd', hb']
    constructor <;> ring
  inv_mem' := by
    rintro γ ⟨hd, hb⟩
    obtain ⟨e00, e01, e10, e11⟩ := SL2Z_inv_apply γ
    show (((γ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = _ ∧ _
    rw [e00, e01, e10, e11]
    push_cast
    exact ⟨by linear_combination -hd, by linear_combination -hb⟩

/-- Γ_ns⁺(N, ε) = {γ ∈ SL₂(ℤ) : γ ≡ [[a, εc], [c, a]] or [[a, −εc], [c, −a]] mod N}. -/
def GammaNsPlus (N : ℕ) (ε : ZMod N) : Subgroup SL(2, ℤ) where
  carrier := {γ | (((γ 1 1 : ℤ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N) ∧
      ((γ 0 1 : ℤ) : ZMod N) = ε * ((γ 1 0 : ℤ) : ZMod N)) ∨
    (((γ 1 1 : ℤ) : ZMod N) = -((γ 0 0 : ℤ) : ZMod N) ∧
      ((γ 0 1 : ℤ) : ZMod N) = -(ε * ((γ 1 0 : ℤ) : ZMod N)))}
  one_mem' := Or.inl (by simp)
  mul_mem' := by
    rintro γ γ' (⟨hd, hb⟩ | ⟨hd, hb⟩) (⟨hd', hb'⟩ | ⟨hd', hb'⟩) <;>
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Int.cast_add, Int.cast_mul, hd, hb, hd', hb']
    · exact Or.inl ⟨by ring, by ring⟩
    · exact Or.inr ⟨by ring, by ring⟩
    · exact Or.inr ⟨by ring, by ring⟩
    · exact Or.inl ⟨by ring, by ring⟩
  inv_mem' := by
    rintro γ h
    obtain ⟨e00, e01, e10, e11⟩ := SL2Z_inv_apply γ
    show ((((γ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = _ ∧ _) ∨ _
    rw [e00, e01, e10, e11]
    push_cast
    rcases h with ⟨hd, hb⟩ | ⟨hd, hb⟩
    · exact Or.inl ⟨by linear_combination -hd, by linear_combination -hb⟩
    · exact Or.inr ⟨by linear_combination hd, by linear_combination -hb⟩

end

end NormalizerLean

-- Part 6, moved verbatim from `NormalizerDelta/DefsGeneral.lean`.

/-!
# General modular curves (2026-10-10): definitions

Definitions for `StatementsGeneral.lean`.  A modular curve of level N is X_H = Γ_H\ℍ* for a subgroup H ≤ SL₂(ℤ/N),
Γ_H = {γ ∈ SL₂(ℤ) : γ mod N ∈ H}.  (For H ≤ GL₂(ℤ/N) with det H = (ℤ/N)ˣ, as in Dose–Lido–Mercuri,
arXiv:2610.08998, Γ_H only depends on H ∩ SL₂(ℤ/N); every congruence subgroup Γ ⊇ Γ(N) is a Γ_H,
`GammaH_map`.)  The statements are about `BG (toR (GammaH N H))` = Nor(Γ_H)/Γ_H.  For −1 ∈ H this is the modular
automorphism group of X_H; for −1 ∉ H the curve's group is the one for H ⊔ {±1} (as for Γ(N) and Γ₁(N) in
`NormalizerDelta/Defs.lean`).

The local conditions are about the reduction of H modulo q ∣ N, computed entrywise with `ZMod.cast`
(for q ∣ N this is the reduction map ℤ/N → ℤ/q; the statements only use it for q ∣ N, or where q ∣ N follows
from the other hypotheses):
* `FixesLine H q v`: every h ∈ H maps v ∈ (ℤ/q)² to a multiple of v;
* `IsBorelMod H q`: H mod q lies in a Borel subgroup, i.e. fixes the line spanned by a unimodular vector
  (for q = p^k: a vector with v mod p ≠ 0);
* `IsSplitMod H q`: H mod q lies in a split Cartan subgroup, i.e. fixes the lines spanned by v and w with
  det [v w] a unit (equivalently: H mod q is conjugate in GL₂(ℤ/q) into the diagonal matrices);
* `FixesUniqueLine H` (prime level): H fixes exactly one line of F_p².
`NormalizerDelta/Defs.lean` and all earlier definitions and statements are unchanged.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- Γ_H = {γ ∈ SL₂(ℤ) : γ mod N ∈ H}, for H ≤ SL₂(ℤ/N). -/
def GammaH (N : ℕ) (H : Subgroup SL(2, ZMod N)) : Subgroup SL(2, ℤ) := H.comap (redSL N)

/-- The normalizer N(H) of H in SL₂(ℤ/N). -/
abbrev NormH {N : ℕ} (H : Subgroup SL(2, ZMod N)) : Subgroup SL(2, ZMod N) :=
  Subgroup.normalizer (H : Set SL(2, ZMod N))

instance {N : ℕ} (H : Subgroup SL(2, ZMod N)) : (H.subgroupOf (NormH H)).Normal :=
  Subgroup.normal_in_normalizer

/-- N(H)/H. -/
abbrev QH {N : ℕ} (H : Subgroup SL(2, ZMod N)) : Type := NormH H ⧸ H.subgroupOf (NormH H)

/-- H mod q fixes the line through v ∈ (ℤ/q)²: for every h ∈ H, (h mod q) v ∈ (ℤ/q)·v. -/
def FixesLine {N : ℕ} (H : Subgroup SL(2, ZMod N)) (q : ℕ) (v : Fin 2 → ZMod q) : Prop :=
  ∀ h ∈ H, ∃ c : ZMod q,
    (h : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ZMod q) *ᵥ v = c • v

/-- H mod q lies in a Borel subgroup of GL₂(ℤ/q): it fixes the line through a unimodular v
(a v₀ + b v₁ = 1 for some a, b). -/
def IsBorelMod {N : ℕ} (H : Subgroup SL(2, ZMod N)) (q : ℕ) : Prop :=
  ∃ v : Fin 2 → ZMod q, (∃ a b : ZMod q, a * v 0 + b * v 1 = 1) ∧ FixesLine H q v

/-- H mod q lies in a split Cartan subgroup of GL₂(ℤ/q): it fixes the lines through v and w, where
det [v w] = v₀w₁ − v₁w₀ is a unit. -/
def IsSplitMod {N : ℕ} (H : Subgroup SL(2, ZMod N)) (q : ℕ) : Prop :=
  ∃ v w : Fin 2 → ZMod q, FixesLine H q v ∧ FixesLine H q w ∧ IsUnit (v 0 * w 1 - v 1 * w 0)

/-- H ≤ SL₂(ℤ/p) fixes exactly one line of (ℤ/p)² (used for p prime). -/
def FixesUniqueLine {p : ℕ} (H : Subgroup SL(2, ZMod p)) : Prop :=
  ∃ v : Fin 2 → ZMod p, v ≠ 0 ∧ FixesLine H p v ∧ ∀ w, FixesLine H p w → ∃ c : ZMod p, w = c • v

/-- The Fricke involution W_p = (1/√p)·[[0, −1], [p, 0]] ∈ SL₂(ℝ). -/
def frickeP (p : ℕ) : SL(2, ℝ) := projSL !![0, -1; (p : ℝ), 0]

end

end NormalizerLean

/-! # Part 7: the normalizer of Γ_Δ(N) for every Δ

Definitions of `NormalizerDelta/StatementsStar.lean` (2026-10-19).  For N ≥ 1 and a subgroup Δ ≤ (ℤ/N)ˣ:
h*_Δ is the largest h such that h² ∣ N, d² ≡ 1 (mod h) for all d ∈ Δ, and Δ contains the kernel of
(ℤ/N)ˣ → (ℤ/(N/h))ˣ; n*_Δ = N/h*_Δ²; D* = diag(h*_Δ, 1).  The statements say that Nor(Γ_Δ(N)) lies between
D*⁻¹Γ₀(n*)D* and D*⁻¹Γ₀(n*)⁺D*, and which Atkin–Lehner elements of level n* it contains. -/

namespace NormalizerLean

noncomputable section

/-- The condition C(h): h ≥ 1, h² ∣ N, d² ≡ 1 (mod h) for every d ∈ Δ, and Δ contains every unit u ≡ 1
(mod N/h), i.e. the kernel of (ℤ/N)ˣ → (ℤ/(N/h))ˣ.  The reductions are `ZMod.cast`, which for h ∣ N and N/h ∣ N
are the reduction maps. -/
def IsHStar (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) (h : ℕ) : Prop :=
  0 < h ∧ h ^ 2 ∣ N ∧ (∀ d ∈ Δ, (ZMod.cast (d : ZMod N) : ZMod h) ^ 2 = 1) ∧
    ∀ u : (ZMod N)ˣ, (ZMod.cast (u : ZMod N) : ZMod (N / h)) = 1 → u ∈ Δ

/-- h*_Δ: the largest h ≤ N with C(h) (`IsHStar`).  For N ≥ 1, h = 1 satisfies C(h), and every h with C(h)
is ≤ N. -/
def hStar (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  haveI := Classical.decPred (IsHStar N Δ)
  Nat.findGreatest (IsHStar N Δ) N

/-- n*_Δ = N / h*_Δ². -/
def nStar (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : ℕ := N / hStar N Δ ^ 2

/-- D* = diag(h*_Δ, 1), rescaled into SL₂(ℝ) by `projSL`. -/
def Dstar (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : SL(2, ℝ) := projSL !![(hStar N Δ : ℝ), 0; 0, 1]

/-- D*⁻¹ Γ₀(n*_Δ) D*. -/
def Gamma0Star (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : Subgroup SL(2, ℝ) :=
  (Gamma0R (nStar N Δ)).map (MulAut.conj (Dstar N Δ)⁻¹).toMonoidHom

/-- M*_Δ = D*⁻¹ Γ₀(n*_Δ)⁺ D* (`Gamma0Plus`: the group generated by the Atkin–Lehner elements of level n*_Δ). -/
def MStar (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : Subgroup SL(2, ℝ) :=
  (Gamma0Plus (nStar N Δ)).map (MulAut.conj (Dstar N Δ)⁻¹).toMonoidHom

/-- u ≡ ι*_Q(d) at level L = N/h*_Δ: for every prime p ∣ L, with q = p^{v_p(L)}, u ≡ d⁻¹ (mod q) if p ∣ Q, and
u ≡ d (mod q) if p ∤ Q.  (ι*_Q inverts the components of (ℤ/L)ˣ = ∏_p (ℤ/p^{v_p(L)})ˣ at the primes of Q.) -/
def IsIotaStar (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) (Q : ℕ) (d u : (ZMod N)ˣ) : Prop :=
  ∀ p ∈ (N / hStar N Δ).primeFactors,
    if p ∣ Q then
      (ZMod.cast (u : ZMod N) : ZMod (p ^ (N / hStar N Δ).factorization p)) *
        (ZMod.cast (d : ZMod N) : ZMod (p ^ (N / hStar N Δ).factorization p)) = 1
    else
      (ZMod.cast (u : ZMod N) : ZMod (p ^ (N / hStar N Δ).factorization p)) =
        (ZMod.cast (d : ZMod N) : ZMod (p ^ (N / hStar N Δ).factorization p))

/-- ι*_Q(Δ̄) = Δ̄, for the image Δ̄ of Δ in (ℤ/(N/h*_Δ))ˣ, spelled out on representatives: u ∈ Δ iff
u ≡ ι*_Q(d) for some d ∈ Δ.  (Δ contains the kernel of (ℤ/N)ˣ → (ℤ/(N/h*_Δ))ˣ, so membership in Δ only depends
on the residue mod N/h*_Δ.) -/
def IsIotaStable (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) (Q : ℕ) : Prop :=
  ∀ u, u ∈ Δ ↔ ∃ d ∈ Δ, IsIotaStar N Δ Q d u

/-- w*_Δ = #{Q ∥ n*_Δ : ι*_Q(Δ̄) = Δ̄}. -/
def wStar (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  Nat.card {Q : ℕ // Q ∣ nStar N Δ ∧ Nat.Coprime Q (nStar N Δ / Q) ∧ IsIotaStable N Δ Q}

end

end NormalizerLean

/-! # Part 8: mixed level

Definitions of `NormalizerDelta/StatementsMixed.lean` (2026-10-19).  For coprime N₁, N₂, H₁ ≤ SL₂(ℤ/N₁) and
H₂ ≤ SL₂(ℤ/N₂), the statements are about Γ = Γ_{H₁}(N₁) ∩ Γ_{H₂}(N₂), which is Γ_H for H = H₁ × H₂ (Chinese
remainder theorem); X_Γ is the fibre product X_{H₁} ×_{X(1)} X_{H₂}.  The new ingredient is Det(H₁), the set of
determinants of the normalizer of H₁ in GL₂(ℤ/N₁). -/

namespace NormalizerLean

noncomputable section

/-- The matrix g ∈ M₂(ℤ/N) normalizes H: for every h ∈ H, g·h = h'·g for some h' ∈ H.  For invertible g this
says gHg⁻¹ ⊆ H, hence gHg⁻¹ = H (H is finite for N ≥ 1): g lies in the normalizer of H in GL₂(ℤ/N). -/
def NormalizesMat {N : ℕ} (H : Subgroup SL(2, ZMod N)) (g : Matrix (Fin 2) (Fin 2) (ZMod N)) : Prop :=
  ∀ h ∈ H, ∃ h' ∈ H, g * (h : Matrix (Fin 2) (Fin 2) (ZMod N)) = (h' : Matrix (Fin 2) (Fin 2) (ZMod N)) * g

/-- u ∈ Det(H): u is the determinant of a matrix normalizing H.  (It is used for units u, and then the matrix
lies in GL₂(ℤ/N).  Det(H) contains every square, from the scalar matrices.) -/
def IsNormDet {N : ℕ} (H : Subgroup SL(2, ZMod N)) (u : ZMod N) : Prop :=
  ∃ g : Matrix (Fin 2) (Fin 2) (ZMod N), g.det = u ∧ NormalizesMat H g

/-- g ∈ SL₂(ℝ) is (det m)^{-1/2}·m for an integral m with det m > 0, det m prime to N₁ and det m mod N₁ ∈ Det(H₁).
(This only depends on g: the integral m with g = projSL m are the positive multiples of one primitive matrix, and
Det(H₁) contains the squares.) -/
def HasNormDet {N₁ : ℕ} (H₁ : Subgroup SL(2, ZMod N₁)) (g : SL(2, ℝ)) : Prop :=
  ∃ m : Matrix (Fin 2) (Fin 2) ℤ, 0 < m.det ∧ g = projSL (m.map (Int.cast : ℤ → ℝ)) ∧
    IsUnit ((m.det : ℤ) : ZMod N₁) ∧ IsNormDet H₁ ((m.det : ℤ) : ZMod N₁)

/-- #{Q ∥ n*_Δ : ι*_Q(Δ̄) = Δ̄ and Q mod N₁ ∈ Det(H₁)}: the Atkin–Lehner classes of Part 7 (`wStar`) that survive
in Γ_{H₁}(N₁) ∩ Γ_Δ(N₂). -/
def wMixed {N₁ : ℕ} (H₁ : Subgroup SL(2, ZMod N₁)) (N₂ : ℕ) (Δ : Subgroup (ZMod N₂)ˣ) : ℕ :=
  Nat.card {Q : ℕ // Q ∣ nStar N₂ Δ ∧ Nat.Coprime Q (nStar N₂ Δ / Q) ∧ IsIotaStable N₂ Δ Q ∧
    IsNormDet H₁ (Q : ZMod N₁)}

/-- The quaternion group Q₈ ≤ SL₂(F₇), generated by [[0, −1], [1, 0]] and [[2, 3], [3, −2]]. -/
def Q8mod7 : Subgroup SL(2, ZMod 7) :=
  Subgroup.closure {⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; decide⟩,
    ⟨!![2, 3; 3, -2], by rw [Matrix.det_fin_two_of]; decide⟩}

end

end NormalizerLean
