import Dubon2026.SourceHeckePrimeComposition
import Dubon2026.SourceBinaryH1HeckeAlgebra

/-! Commutativity of the full original good-prime binary H1 correspondences.
DUB-17/18 -> residual modular Galois association -> original residual H1
eigensystem -> prescribed-character realization. This discharges its remaining
commutativity premise on the actual integral operators, in every binary degree.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

private theorem binaryDiagonal_comp_commute (R : Type) [CommRing R] (w p q : ℕ) :
    (homogeneousMatrixAction w (Matrix.diagonal ![(p : R), 1])).comp
        (homogeneousMatrixAction w (Matrix.diagonal ![(q : R), 1])) =
      (homogeneousMatrixAction w (Matrix.diagonal ![(q : R), 1])).comp
        (homogeneousMatrixAction w (Matrix.diagonal ![(p : R), 1])) := by
  have hm : Matrix.diagonal ![(p : R), 1] * Matrix.diagonal ![(q : R), 1] =
      Matrix.diagonal ![(q : R), 1] * Matrix.diagonal ![(p : R), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  have h := congrArg (homogeneousMatrixRepresentation (R := R) w) hm
  simpa only [map_mul] using h

/-- The genuine full binary H1 Hecke operators at every pair of good primes
commute over the actual coefficient ring. Product-coset factorization and all
coboundary corrections are derived for these original operators. -/
theorem sourceBinaryHeckeH1_commute (R : Type) [CommRing R] {Q p q : ℕ}
    [NeZero p] [NeZero q] (hp : p.Prime) (hq : q.Prime)
    (hpQ : Nat.Coprime p Q) (hqQ : Nat.Coprime q Q) (w : ℕ) :
    Commute (sourceBinaryHeckeH1 (Q := Q) R hp w) (sourceBinaryHeckeH1 R hq w) := by
  by_cases hpq : p = q
  · subst q
    exact Commute.refl _
  · have hcop : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr (by
      intro h
      exact hpq ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one))
    apply LinearMap.ext
    intro x
    change sourceBinaryHeckeH1 R hp w (sourceBinaryHeckeH1 R hq w x) =
      sourceBinaryHeckeH1 R hq w (sourceBinaryHeckeH1 R hp w x)
    refine groupCohomology.H1_induction_on x ?_
    intro c
    rw [sourceBinaryHeckeH1_cocycle, sourceBinaryHeckeH1_cocycle,
      sourceBinaryHeckeH1_cocycle, sourceBinaryHeckeH1_cocycle]
    apply (groupCohomology.H1π_eq_iff _ _).mpr
    letI : Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q p) := sourceHeckeUpperFintype Q p
    letI : Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q q) := sourceHeckeUpperFintype Q q
    exact sourceHeckePrimeCommutator_mem hp hq hpQ hqQ hcop (sourceBinaryCoefficientRep R Q w)
      (homogeneousMatrixAction w (Matrix.diagonal ![(p : R), 1]))
      (homogeneousMatrixAction w (Matrix.diagonal ![(q : R), 1]))
      (sourceBinaryHeckeDiagonal_intertwine R hp w)
      (sourceBinaryHeckeDiagonal_intertwine R hq w)
      (binaryDiagonal_comp_commute R w p q) c

/-- Every pair of generators of the actual full integral H1 Hecke algebra
commutes, with no assumed commutative algebra structure or eigensystem. -/
theorem sourceBinaryH1PrimeOperators_commute (R : Type) [CommRing R] (Q w : ℕ)
    (p q : sourceBinaryHeckePrime Q) :
    Commute (sourceBinaryH1PrimeOperators R Q w p) (sourceBinaryH1PrimeOperators R Q w q) := by
  letI : NeZero p.val := ⟨p.property.1.ne_zero⟩
  letI : NeZero q.val := ⟨q.property.1.ne_zero⟩
  exact sourceBinaryHeckeH1_commute R p.property.1 q.property.1
    p.property.2 q.property.2 w

end
end Dubon2026
