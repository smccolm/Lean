import GafniTao.WooleySection7Coefficient
import GafniTao.WooleyTupleDisplacement

/-!
# The exact tuple form of Wooley equation (7.17)

After expanding the two absolute moments, a summand is indexed by the four
ordered tuple families `(u,z,v,w)`.  The original `alpha` average imposes the
combined displacement for `(u,z)` and `(v,w)`; the inserted `beta` average
imposes the lower-degree displacement for `(u,z)` alone.  This file proves
the insertion exactly from the source congruence implication (7.12).

The implication is exposed as a pointwise hypothesis here.  It is not the
target mean-value estimate and will be discharged by the Section 7
translation/determinant argument before Corollary 3.2 is assembled.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

abbrev WooleySourceTuplePair (s : ℕ) (gamma : WooleySourceSequence) :=
  WooleyFiniteTuple s (↑gamma.support) ×
    WooleyFiniteTuple s (↑gamma.support)

abbrev WooleySourceMixedTuple (R S : ℕ)
    (left right : WooleySourceSequence) :=
  WooleySourceTuplePair R left × WooleySourceTuplePair S right

/-- Coefficient product belonging to `(u,z,v,w)`. -/
def wooleySourceMixedTupleCoefficient
    (R S : ℕ) (left right : WooleySourceSequence)
    (omega : WooleySourceMixedTuple R S left right) : ℂ :=
  wooleyTupleCoefficient R (fun n : ↑left.support => left n) omega.1 *
    wooleyTupleCoefficient S (fun n : ↑right.support => right n) omega.2

/-- Polynomial displacement of a tuple pair drawn from a source support. -/
def wooleySourceTuplePolynomialDisplacement {k : ℕ}
    (phi : WooleyPolynomialSystem k) (q s : ℕ)
    (gamma : WooleySourceSequence) (xy : WooleySourceTuplePair s gamma) :
    Fin k → ZMod q :=
  wooleyTupleDisplacement q k s
    (fun n : ↑gamma.support => wooleyPolynomialValue phi q (n : ℤ)) xy

/-- The displacement imposed by the original `alpha` average in (7.17). -/
def wooleyEquation717OriginalDisplacement {k : ℕ}
    (leftPhi rightPhi : WooleyPolynomialSystem k) (q R S : ℕ)
    (left right : WooleySourceSequence)
    (omega : WooleySourceMixedTuple R S left right) : Fin k → ZMod q :=
  fun j =>
    wooleySourceTuplePolynomialDisplacement
        leftPhi q R left omega.1 j +
      wooleySourceTuplePolynomialDisplacement
        rightPhi q S right omega.2 j

/-- The lower-degree displacement imposed by the redundant `beta` average. -/
def wooleyEquation717InsertedDisplacement {r : ℕ}
    (psi : WooleyPolynomialSystem r) (qPrime R S : ℕ)
    (left right : WooleySourceSequence)
    (omega : WooleySourceMixedTuple R S left right) : Fin r → ZMod qPrime :=
  wooleySourceTuplePolynomialDisplacement psi qPrime R left omega.1

/-- Exact finite Fourier insertion underlying (7.17).  The hypothesis is the
literal implication that the original congruence system forces (7.12). -/
theorem wooley_equation_7_17_tuple
    {k r : ℕ} (leftPhi rightPhi : WooleyPolynomialSystem k)
    (psi : WooleyPolynomialSystem r)
    (q qPrime R S : ℕ) [NeZero q] [NeZero qPrime]
    (left right : WooleySourceSequence)
    (h712 : ∀ omega : WooleySourceMixedTuple R S left right,
      wooleyEquation717OriginalDisplacement
          leftPhi rightPhi q R S left right omega = 0 →
        wooleyEquation717InsertedDisplacement
          psi qPrime R S left right omega = 0) :
    ((((q ^ k : ℕ) : ℂ))⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          ∑ omega : WooleySourceMixedTuple R S left right,
            wooleySourceMixedTupleCoefficient R S left right omega *
              ∏ j, ZMod.stdAddChar
                (alpha j * wooleyEquation717OriginalDisplacement
                  leftPhi rightPhi q R S left right omega j) =
      ((((q ^ k : ℕ) : ℂ))⁻¹) *
        ((((qPrime ^ r : ℕ) : ℂ))⁻¹) *
          ∑ alpha : Fin k → ZMod q,
            ∑ beta : Fin r → ZMod qPrime,
              ∑ omega : WooleySourceMixedTuple R S left right,
                wooleySourceMixedTupleCoefficient R S left right omega *
                  (∏ j, ZMod.stdAddChar
                    (alpha j * wooleyEquation717OriginalDisplacement
                      leftPhi rightPhi q R S left right omega j)) *
                  ∏ l, ZMod.stdAddChar
                    (beta l * wooleyEquation717InsertedDisplacement
                      psi qPrime R S left right omega l) := by
  exact wooley_insert_redundant_grid_average q k qPrime r
    (wooleySourceMixedTupleCoefficient R S left right)
    (wooleyEquation717OriginalDisplacement
      leftPhi rightPhi q R S left right)
    (wooleyEquation717InsertedDisplacement
      psi qPrime R S left right)
    h712

#print axioms wooleySourceMixedTupleCoefficient
#print axioms wooleySourceTuplePolynomialDisplacement
#print axioms wooleyEquation717OriginalDisplacement
#print axioms wooleyEquation717InsertedDisplacement
#print axioms wooley_equation_7_17_tuple

end

end GafniTao
