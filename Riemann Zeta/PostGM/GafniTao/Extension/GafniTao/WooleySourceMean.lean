import GafniTao.WooleyPolynomialSystem

/-!
# Wooley's source-level finitely supported means

The degree induction in Section 7 of Wooley's nested efficient congruencing
argument translates a residue class `n = p^a y + xi`.  The resulting
coefficient family is naturally indexed by all integers, not by a fixed box
`Fin Q`.  This file therefore gives the literal finite-support integer model
needed for Corollary 3.2 and its recursive use.

All integrals are the exact finite Fourier averages from (3.5).  A
`Finsupp` is used only to package finite support; it introduces no convergence
or summability assumption.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The source coefficient sequences `D_0`, restricted to finite support as
is sufficient for every application in Sections 4--12. -/
abbrev WooleySourceSequence := ℤ →₀ ℂ

/-- The pointwise bound in Wooley's class `D_0`.  Absolute summability is
automatic for `Finsupp`. -/
def WooleySourceSequence.Admissible (gamma : WooleySourceSequence) : Prop :=
  ∀ n : ℤ, ‖gamma n‖ ≤ 1

/-- The square of `rho_0` in (3.2). -/
def wooleySourceMassSq (gamma : WooleySourceSequence) : ℝ :=
  ∑ n ∈ gamma.support, ‖gamma n‖ ^ 2

/-- The square of `rho_h(xi)` in (3.2). -/
def wooleySourceResidueMassSq (gamma : WooleySourceSequence)
    (q : ℕ) (xi : ZMod q) : ℝ :=
  ∑ n ∈ gamma.support.filter (fun n : ℤ => (n : ZMod q) = xi),
    ‖gamma n‖ ^ 2

/-- The polynomial phase in (3.3), on the exact integer support. -/
def wooleySourcePolynomialPhase {k q : ℕ} [NeZero q]
    (phi : WooleyPolynomialSystem k) (alpha : Fin k → ZMod q)
    (n : ℤ) : ℂ :=
  ZMod.stdAddChar
    (∑ j : Fin k, alpha j * (((phi j).eval n : ℤ) : ZMod q))

/-- The unnormalised global exponential sum. -/
def wooleySourcePolynomialSum {k q : ℕ} [NeZero q]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod q) : ℂ :=
  ∑ n ∈ gamma.support, gamma n * wooleySourcePolynomialPhase phi alpha n

/-- The unnormalised residue-class exponential sum. -/
def wooleySourcePolynomialResidueSum {k q qH : ℕ} [NeZero q]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod q) (xi : ZMod qH) : ℂ :=
  ∑ n ∈ gamma.support.filter (fun n : ℤ => (n : ZMod qH) = xi),
    gamma n * wooleySourcePolynomialPhase phi alpha n

/-- The normalised sum `f_gamma` from (3.3). -/
def wooleySourceNormalizedPolynomialSum {k q : ℕ} [NeZero q]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod q) : ℂ :=
  if wooleySourceMassSq gamma = 0 then 0
  else ((Real.sqrt (wooleySourceMassSq gamma) : ℂ)⁻¹) *
    wooleySourcePolynomialSum phi gamma alpha

/-- The normalised residue sum `f_h(alpha;xi)` from (3.4). -/
def wooleySourceNormalizedPolynomialResidueSum {k q qH : ℕ} [NeZero q]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod q) (xi : ZMod qH) : ℂ :=
  if wooleySourceResidueMassSq gamma qH xi = 0 then 0
  else ((Real.sqrt (wooleySourceResidueMassSq gamma qH xi) : ℂ)⁻¹) *
    wooleySourcePolynomialResidueSum phi gamma alpha xi

/-- The finite Fourier-average realization of `U^B_{s,k}` in (3.6), with
the modulus supplied explicitly. -/
def wooleySourcePolynomialMean {k : ℕ} (s q : ℕ) [NeZero q]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence) : ℝ :=
  ((q ^ k : ℕ) : ℝ)⁻¹ *
    ∑ alpha : Fin k → ZMod q,
      ‖wooleySourceNormalizedPolynomialSum phi gamma alpha‖ ^ (2 * s)

/-- The finite Fourier-average realization of `U^{B,h}_{s,k}` in (3.8). -/
def wooleySourcePolynomialConditionedMean {k : ℕ}
    (s q qH : ℕ) [NeZero q] [NeZero qH]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence) : ℝ :=
  if wooleySourceMassSq gamma = 0 then 0
  else (wooleySourceMassSq gamma)⁻¹ *
    ∑ xi : ZMod qH,
      wooleySourceResidueMassSq gamma qH xi *
        (((q ^ k : ℕ) : ℝ)⁻¹ *
          ∑ alpha : Fin k → ZMod q,
            ‖wooleySourceNormalizedPolynomialResidueSum
              phi gamma alpha xi‖ ^ (2 * s))

/-- The exact source class `Phi_tau(B)`: some coefficient depth `c` is at
least `tau B`, and the system is `p^c`-spaced. -/
def WooleyPolynomialSystem.InPhiTau {k : ℕ}
    (phi : WooleyPolynomialSystem k) (p B : ℕ) (tau : ℝ) : Prop :=
  ∃ c : ℕ, phi.Spaced p c ∧ tau * (B : ℝ) ≤ (c : ℝ)

/-- The exact finite-support form of Wooley Corollary 3.2 at fixed `k,p`.
This is a target proposition, not a postulate.  Its eventual proof is the
output of Sections 6--10. -/
def WooleyPolynomialCorollary32At (k p : ℕ) [NeZero p] : Prop :=
  ∀ tau epsilon : ℝ, 0 < tau → 0 < epsilon →
    ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
      ∀ (B : ℕ) (phi : WooleyPolynomialSystem k)
        (gamma : WooleySourceSequence),
        B0 ≤ B → phi.InPhiTau p B tau → gamma.Admissible →
          wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B)
              phi gamma ≤
            C * (p ^ B : ℝ) ^ epsilon *
              wooleySourcePolynomialConditionedMean
                (wooleyTriangular k) (p ^ B)
                  (p ^ (B ⌈/⌉ k)) phi gamma

/-- Wooley Corollary 3.2 with its source hypotheses and the prime-induced
nonzero-modulus instance made explicit. -/
def WooleyPolynomialCorollary32 : Prop :=
  ∀ (k p : ℕ) (hp : Nat.Prime p), 1 ≤ k → k < p →
    @WooleyPolynomialCorollary32At k p ⟨hp.ne_zero⟩

theorem wooleySourceMassSq_nonneg (gamma : WooleySourceSequence) :
    0 ≤ wooleySourceMassSq gamma := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem wooleySourceResidueMassSq_nonneg (gamma : WooleySourceSequence)
    (q : ℕ) (xi : ZMod q) :
    0 ≤ wooleySourceResidueMassSq gamma q xi := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Residue classes partition the source sequence's `L²` mass exactly. -/
theorem wooleySource_sum_residueMassSq (gamma : WooleySourceSequence)
    (q : ℕ) [NeZero q] :
    ∑ xi : ZMod q, wooleySourceResidueMassSq gamma q xi =
      wooleySourceMassSq gamma := by
  unfold wooleySourceResidueMassSq wooleySourceMassSq
  rw [Finset.sum_fiberwise
    (s := gamma.support)
    (g := fun n : ℤ => (n : ZMod q))
    (f := fun n : ℤ => ‖gamma n‖ ^ 2)]

/-- The unnormalised residue pieces sum back to the global polynomial sum. -/
theorem wooleySource_sum_residuePolynomialSum {k q qH : ℕ}
    [NeZero q] [NeZero qH] (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) (alpha : Fin k → ZMod q) :
    ∑ xi : ZMod qH,
        wooleySourcePolynomialResidueSum phi gamma alpha xi =
      wooleySourcePolynomialSum phi gamma alpha := by
  unfold wooleySourcePolynomialResidueSum wooleySourcePolynomialSum
  rw [Finset.sum_fiberwise
    (s := gamma.support)
    (g := fun n : ℤ => (n : ZMod qH))
    (f := fun n : ℤ =>
      gamma n * wooleySourcePolynomialPhase phi alpha n)]

#print axioms wooleySourceMassSq_nonneg
#print axioms wooleySourceResidueMassSq_nonneg
#print axioms wooleySource_sum_residueMassSq
#print axioms wooleySource_sum_residuePolynomialSum

end

end GafniTao
