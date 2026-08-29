import RiemannZeta.GuthMaynard.KloostermanArtinSchreier

/-!
# Trace parametrization of the Harcos Kloosterman curve

This module proves the exact algebraic change of variables behind Harcos
equation (3).  For nonzero `c` in odd characteristic, the affine curve

`y² = (x^p-x)² - 4c`

is equivalent to pairs `(x,t)` with `t` a unit and
`x^p-x = t+c/t`.
-/

namespace RiemannZeta.GuthMaynard

open scoped BigOperators
open Classical
open Polynomial

/-- The `QuadraticArtinCurvePoints` definition used by the source-facing construction in `KloostermanCurveTrace`. -/
abbrev QuadraticArtinCurvePoints {F : Type*} [Field F]
    (p : ℕ) (c : F) :=
  {z : F × F // z.2 ^ 2 = (z.1 ^ p - z.1) ^ 2 - 4 * c}

/-- The `ArtinUnitPoints` definition used by the source-facing construction in `KloostermanCurveTrace`. -/
abbrev ArtinUnitPoints {F : Type*} [Field F]
    (p : ℕ) (c : F) :=
  {z : F × Fˣ // z.1 ^ p - z.1 = (z.2 : F) + c / (z.2 : F)}

/-- The `quadraticArtinCurveEquivUnitPoints` definition used by the source-facing construction in `KloostermanCurveTrace`. -/
noncomputable def quadraticArtinCurveEquivUnitPoints
    {F : Type*} [Field F] (p : ℕ) (c : F) (hc : c ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    QuadraticArtinCurvePoints p c ≃ ArtinUnitPoints p c where
  toFun z := by
    let u := z.1.1 ^ p - z.1.1
    let t : F := (u + z.1.2) / 2
    have ht : t ≠ 0 := by
      intro htz
      have hsum : u + z.1.2 = 0 := (div_eq_zero_iff).mp htz |>.resolve_right h2
      have hy : z.1.2 = -u := by linear_combination hsum
      have hz := z.2
      dsimp [u] at hy ⊢
      rw [hy] at hz
      have h4 : (4 : F) ≠ 0 := by
        rw [show (4 : F) = 2 * 2 by norm_num]
        exact mul_ne_zero h2 h2
      apply hc
      apply (mul_eq_zero.mp ?_).resolve_left h4
      linear_combination hz
    refine ⟨(z.1.1, Units.mk0 t ht), ?_⟩
    change u = t + c / t
    have hz := z.2
    have hprod : (u + z.1.2) * (u - z.1.2) = 4 * c := by
      dsimp [u] at hz ⊢
      linear_combination -hz
    have hquot : c / t = (u - z.1.2) / 2 := by
      apply (div_eq_iff ht).2
      dsimp [t]
      field_simp [h2]
      dsimp [u] at hprod
      linear_combination -hprod
    rw [hquot]
    dsimp [t]
    field_simp [h2]
    ring
  invFun z := by
    let u := z.1.1 ^ p - z.1.1
    let t : F := z.1.2
    refine ⟨(z.1.1, 2 * t - u), ?_⟩
    change (2 * t - u) ^ 2 = u ^ 2 - 4 * c
    have hz := z.2
    change u = t + c / t at hz
    have ht : t ≠ 0 := z.1.2.ne_zero
    field_simp at hz
    linear_combination -4 * hz
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [h2]
      ring
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Units.ext
      dsimp
      field_simp [h2]
      ring

/-- The `artinUnitEquivSigmaFiber` definition used by the source-facing construction in `KloostermanCurveTrace`. -/
noncomputable def artinUnitEquivSigmaFiber
    (p n : ℕ) [Fact p.Prime] (c : GaloisField p n) :
    ArtinUnitPoints p c ≃
      (t : (GaloisField p n)ˣ) ×
        ArtinSchreierFiber p n ((t : GaloisField p n) + c / (t : GaloisField p n)) where
  toFun z := ⟨z.1.2, ⟨z.1.1, by
    rw [artinSchreierLinear_apply]
    exact z.2⟩⟩
  invFun z := ⟨(z.2.1, z.1), by
    rw [← artinSchreierLinear_apply]
    exact z.2.2⟩
  left_inv z := by rfl
  right_inv z := by rfl

theorem card_artinSchreierFiber
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (b : GaloisField p n) :
    Nat.card (ArtinSchreierFiber p n b) =
      if Algebra.trace (ZMod p) (GaloisField p n) b = 0 then p else 0 := by
  split_ifs with hb
  · exact card_artinSchreierFiber_of_trace_eq_zero p n hn b hb
  · haveI : IsEmpty (ArtinSchreierFiber p n b) := ⟨by
      intro x
      have hmem : b ∈ (artinSchreierLinear p n).range := ⟨x, x.2⟩
      rw [artin_range_eq_trace_ker p n hn, LinearMap.mem_ker] at hmem
      exact hb hmem⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

theorem sum_stdAddChar_mul (p : ℕ) [NeZero p] [Fact p.Prime]
    (A : ZMod p) :
    (∑ m : ZMod p, ZMod.stdAddChar (m * A)) =
      if A = 0 then (p : ℂ) else 0 := by
  by_cases hA : A = 0
  · subst A
    simp [ZMod.card p]
  · rw [if_neg hA]
    simpa [mul_comm] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hA))

/-- The `extensionKloostermanScalarSum` definition used by the source-facing construction in `KloostermanCurveTrace`. -/
noncomputable def extensionKloostermanScalarSum
    (p n : ℕ) [Fact p.Prime] (c : GaloisField p n) (m : ZMod p) : ℂ :=
  by
    letI := Fintype.ofFinite (GaloisField p n)
    exact ∑ t : (GaloisField p n)ˣ,
      ZMod.stdAddChar
        (m * Algebra.trace (ZMod p) (GaloisField p n)
          ((t : GaloisField p n) + c / (t : GaloisField p n)))

theorem card_quadraticArtinCurve_eq_scalarSums
    (p n : ℕ) [Fact p.Prime] (hpodd : Odd p) (hn : n ≠ 0)
    (c : GaloisField p n) (hc : c ≠ 0) :
    (Nat.card (QuadraticArtinCurvePoints p c) : ℂ) =
      ∑ m : ZMod p, extensionKloostermanScalarSum p n c m := by
  letI := Fintype.ofFinite (GaloisField p n)
  letI : NeZero p := ⟨(show p.Prime from Fact.out).ne_zero⟩
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro htwo
    have hpdiv : p ∣ 2 :=
      (CharP.cast_eq_zero_iff (GaloisField p n) p 2).mp htwo
    have hpeq : p = 2 :=
      (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hpdiv
        |>.resolve_left (show p.Prime from Fact.out).ne_one
    subst p
    norm_num at hpodd
  rw [Nat.card_congr (quadraticArtinCurveEquivUnitPoints p c hc h2)]
  rw [Nat.card_congr (artinUnitEquivSigmaFiber p n c)]
  rw [Nat.card_sigma]
  simp_rw [card_artinSchreierFiber p n hn]
  push_cast
  simp_rw [← sum_stdAddChar_mul p]
  rw [Finset.sum_comm]
  simp [extensionKloostermanScalarSum]

theorem eval_kloostermanCurvePolynomial
    (p n : ℕ) [Fact p.Prime] (c : ZMod p) (x : GaloisField p n) :
    (kloostermanCurvePolynomial p n c).eval x =
      (x ^ p - x) ^ 2 - 4 * algebraMap (ZMod p) (GaloisField p n) c := by
  simp only [kloostermanCurvePolynomial, kloostermanArtinSchreier,
    eval_sub, eval_pow, eval_X, eval_C]
  rw [map_mul]
  rw [map_ofNat]

theorem card_quadraticArtinCurve_eq_hyperelliptic
    (p n : ℕ) [Fact p.Prime] (c : ZMod p) :
    letI := Fintype.ofFinite (GaloisField p n)
    Nat.card (QuadraticArtinCurvePoints p
      (algebraMap (ZMod p) (GaloisField p n) c)) =
      (hyperellipticAffinePointFinset
        (kloostermanCurvePolynomial p n c)).card := by
  classical
  letI := Fintype.ofFinite (GaloisField p n)
  rw [Nat.card_eq_fintype_card]
  let s := hyperellipticAffinePointFinset
    (kloostermanCurvePolynomial p n c)
  let e : QuadraticArtinCurvePoints p
      (algebraMap (ZMod p) (GaloisField p n) c) ≃ ↑s :=
    { toFun := fun z => ⟨z.1, by
        simpa [s, hyperellipticAffinePointFinset,
          eval_kloostermanCurvePolynomial] using z.2⟩
      invFun := fun z => ⟨z.1, by
        simpa [s, hyperellipticAffinePointFinset,
          eval_kloostermanCurvePolynomial] using z.2⟩
      left_inv := fun z => by rfl
      right_inv := fun z => by rfl }
  calc
    Fintype.card (QuadraticArtinCurvePoints p
        (algebraMap (ZMod p) (GaloisField p n) c)) = Fintype.card ↑s :=
      Fintype.card_congr e
    _ = s.card := Fintype.card_coe s

end RiemannZeta.GuthMaynard
