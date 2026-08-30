import RiemannZeta.GuthMaynard.KloostermanTraceInverse
import Mathlib.FieldTheory.Finite.Extension

/-!
# Closed points and extension-field roots

This file proves the finite-field closed-point correspondence required to
turn Harcos equation (10) into equation (8).  The correspondence is between
elements of `GaloisField p n` and a monic irreducible polynomial whose degree
divides `n`, together with a chosen root of that polynomial.  The zero element
is retained: it is the root of `X`, and its later character contribution is
zero.
-/

open Polynomial Classical

namespace RiemannZeta.GuthMaynard

/-- The `harcosRootEmbedding` definition used by the source-facing construction in `KloostermanClosedPoints`. -/
noncomputable def harcosRootEmbedding
    (p n d : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (q : HarcosIrreducibleMonicDegree p d) (hd : d ∣ n) :
    AdjoinRoot q.1.1 →ₐ[ZMod p] GaloisField p n := by
  letI : Fact (Irreducible q.1.1) := ⟨q.1.2.1⟩
  apply Classical.choice
  apply FiniteField.nonempty_algHom_of_finrank_dvd
  rw [(AdjoinRoot.powerBasis q.1.2.1.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim, q.2, GaloisField.finrank p hn]
  exact hd

/-- The `harcosChosenRoot` definition used by the source-facing construction in `KloostermanClosedPoints`. -/
noncomputable def harcosChosenRoot
    (p n d : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (q : HarcosIrreducibleMonicDegree p d) (hd : d ∣ n) :
    GaloisField p n :=
  harcosRootEmbedding p n d hn q hd (AdjoinRoot.root q.1.1)

theorem aeval_harcosChosenRoot
    (p n d : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (q : HarcosIrreducibleMonicDegree p d) (hd : d ∣ n) :
    Polynomial.aeval (harcosChosenRoot p n d hn q hd) q.1.1 = 0 := by
  letI : Fact (Irreducible q.1.1) := ⟨q.1.2.1⟩
  unfold harcosChosenRoot
  rw [Polynomial.aeval_algHom_apply]
  rw [AdjoinRoot.aeval_eq]
  simp

theorem minpoly_harcosChosenRoot
    (p n d : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (q : HarcosIrreducibleMonicDegree p d) (hd : d ∣ n) :
    minpoly (ZMod p) (harcosChosenRoot p n d hn q hd) = q.1.1 := by
  symm
  exact minpoly.eq_of_irreducible_of_monic q.1.2.1
    (aeval_harcosChosenRoot p n d hn q hd) q.1.2.2

theorem splits_harcosIrreducibleMonicDegree
    (p n d : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (q : HarcosIrreducibleMonicDegree p d) (hd : d ∣ n) :
    (q.1.1.map (algebraMap (ZMod p) (GaloisField p n))).Splits := by
  rw [← minpoly_harcosChosenRoot p n d hn q hd]
  exact IsGalois.splits (ZMod p) (harcosChosenRoot p n d hn q hd)

theorem card_rootSet_harcosIrreducibleMonicDegree
    (p n d : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (q : HarcosIrreducibleMonicDegree p d) (hd : d ∣ n) :
    Fintype.card (q.1.1.rootSet (GaloisField p n)) = d := by
  calc
    Fintype.card (q.1.1.rootSet (GaloisField p n)) = q.1.1.natDegree :=
      card_rootSet_eq_natDegree
        (PerfectField.separable_of_irreducible q.1.2.1)
        (splits_harcosIrreducibleMonicDegree p n d hn q hd)
    _ = d := q.2

theorem minpoly_natDegree_dvd_galoisField_degree
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (x : GaloisField p n) :
    (minpoly (ZMod p) x).natDegree ∣ n := by
  letI := Fintype.ofFinite (GaloisField p n)
  have hcard : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p n hn
  have hroot : Polynomial.aeval x
      (X ^ (Nat.card (ZMod p)) ^ n - X : (ZMod p)[X]) = 0 := by
    have hxpow : x ^ p ^ n = x := by
      rw [← hcard]
      exact FiniteField.pow_card x
    simp only [aeval_sub, aeval_X_pow, aeval_X, Nat.card_zmod]
    rw [hxpow, sub_self]
  exact Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
    (minpoly.irreducible (Algebra.IsIntegral.isIntegral x))
    (minpoly.dvd (ZMod p) x hroot)

theorem minpoly_natDegree_le_galoisField_degree
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (x : GaloisField p n) :
    (minpoly (ZMod p) x).natDegree ≤ n := by
  calc
    (minpoly (ZMod p) x).natDegree ≤
        Module.finrank (ZMod p) (GaloisField p n) := minpoly.natDegree_le x
    _ = n := GaloisField.finrank p hn

/-- The `HarcosClosedPointRoot` definition used by the source-facing construction in `KloostermanClosedPoints`. -/
def HarcosClosedPointRoot
    (p n : ℕ) [Fact p.Prime] :=
  Σ q : HarcosPrimeDividingDegree p n,
    q.1.1.1.rootSet (GaloisField p n)

noncomputable instance harcosClosedPointRootFintype
    (p n : ℕ) [Fact p.Prime] :
    Fintype (HarcosClosedPointRoot p n) := by
  unfold HarcosClosedPointRoot
  infer_instance

/-- The `galoisFieldToClosedPoint` definition used by the source-facing construction in `KloostermanClosedPoints`. -/
noncomputable def galoisFieldToClosedPoint
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (x : GaloisField p n) :
    HarcosClosedPointRoot p n := by
  let q : HarcosIrreducibleMonic p :=
    ⟨minpoly (ZMod p) x,
      minpoly.irreducible (Algebra.IsIntegral.isIntegral x),
      minpoly.monic (Algebra.IsIntegral.isIntegral x)⟩
  let qUp : HarcosPrimeUpTo p n :=
    ⟨q, minpoly_natDegree_le_galoisField_degree p n hn x⟩
  let qDiv : HarcosPrimeDividingDegree p n :=
    ⟨qUp, minpoly_natDegree_dvd_galoisField_degree p n hn x⟩
  exact ⟨qDiv, ⟨x, by
    exact (minpoly.monic (Algebra.IsIntegral.isIntegral x)).mem_rootSet.mpr
      (minpoly.aeval (ZMod p) x)⟩⟩

/-- The `harcosClosedPointEquiv` definition used by the source-facing construction in `KloostermanClosedPoints`. -/
noncomputable def harcosClosedPointEquiv
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    GaloisField p n ≃ HarcosClosedPointRoot p n where
  toFun := galoisFieldToClosedPoint p n hn
  invFun z := z.2.1
  left_inv _ := rfl
  right_inv z := by
    apply Sigma.subtype_ext
    · apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      symm
      exact minpoly.eq_of_irreducible_of_monic z.1.1.1.2.1
        (z.1.1.1.2.2.mem_rootSet.mp z.2.2) z.1.1.1.2.2
    · rfl

end RiemannZeta.GuthMaynard
