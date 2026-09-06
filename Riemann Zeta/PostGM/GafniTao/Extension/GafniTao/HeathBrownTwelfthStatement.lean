import GafniTao.HeathBrownZetaPattern
import GafniTao.HeathBrownLogAbsorption

/-!
# Heath--Brown's discrete twelfth-moment large-values statement

The source theorem is Heath--Brown (1978), Theorem 2, equation (7).  The
definition below records its literal finite-set formulation: absolute-height
cutoff, unit separation, critical-line zeta values, and the power
`T^2 V^(-12) log(T)^16`.  No instance of the statement is postulated here.
-/

open Complex Finset Set

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The absolute value of zeta on the critical line in the sign convention of
Heath--Brown's Theorem 2. -/
noncomputable def heathBrownCriticalZetaNorm (t : Real) : Real :=
  ‖riemannZeta (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I)‖

/-- The exact hypotheses on a finite family of large critical-line values in
Heath--Brown's Theorem 2. -/
def HeathBrownTwelfthPacket
    (T V : Real) (W : Finset Real) : Prop :=
  IsSeparated 1 W ∧
  (∀ t ∈ W, |t| ≤ T) ∧
  (∀ t ∈ W, V ≤ heathBrownCriticalZetaNorm t)

/-- Heath--Brown (1978), Theorem 2, equation (7), with the Vinogradov
constant exposed.  The theorem is deliberately a proposition until its
analytic proof is assembled in the subsequent modules. -/
def HeathBrownDiscreteTwelfthMoment : Prop :=
  ∃ C : Real, 0 < C ∧
    ∀ (T V : Real) (W : Finset Real),
      2 ≤ T → 0 < V → HeathBrownTwelfthPacket T V W →
      (W.card : Real) ≤
        C * T ^ (2 : Nat) / V ^ (12 : Nat) *
          Real.log T ^ (16 : Nat)

/-- The dyadic positive-height version is an exact specialization of the
source theorem; no endpoint or separation loss occurs. -/
theorem heathBrownDiscreteTwelfthMoment_dyadic
    (hHB : HeathBrownDiscreteTwelfthMoment) :
    ∃ C : Real, 0 < C ∧
      ∀ (T V : Real) (W : Finset Real),
        2 ≤ T → 0 < V → IsSeparated 1 W →
        (∀ t ∈ W, T / 2 ≤ t ∧ t ≤ T) →
        (∀ t ∈ W, V ≤ heathBrownCriticalZetaNorm t) →
        (W.card : Real) ≤
          C * T ^ (2 : Nat) / V ^ (12 : Nat) *
            Real.log T ^ (16 : Nat) := by
  obtain ⟨C, hC, hbound⟩ := hHB
  refine ⟨C, hC, ?_⟩
  intro T V W hT hV hSep hRange hLarge
  apply hbound T V W hT hV
  refine ⟨hSep, ?_, hLarge⟩
  intro t ht
  have htRange := hRange t ht
  rw [abs_of_nonneg (by linarith : 0 ≤ t)]
  exact htRange.2

/-- The right side of the discrete theorem is nonnegative on its source
range.  This small fact is used repeatedly when finite subfamilies are
discarded. -/
theorem heathBrownTwelfthMajorant_nonneg
    {C T V : Real} (hC : 0 ≤ C) (hT : 1 ≤ T) (hV : 0 < V) :
    0 ≤ C * T ^ (2 : Nat) / V ^ (12 : Nat) *
      Real.log T ^ (16 : Nat) := by
  positivity

/-- Equation (7) is stable under passing to a subfamily. -/
theorem heathBrownTwelfthPacket_subset
    {T V : Real} {W S : Finset Real}
    (hpacket : HeathBrownTwelfthPacket T V W) (hSW : S ⊆ W) :
    HeathBrownTwelfthPacket T V S := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hpacket.1 x (hSW hx) y (hSW hy) hxy
  · intro t ht
    exact hpacket.2.1 t (hSW ht)
  · intro t ht
    exact hpacket.2.2 t (hSW ht)

#print axioms heathBrownDiscreteTwelfthMoment_dyadic
#print axioms heathBrownTwelfthMajorant_nonneg
#print axioms heathBrownTwelfthPacket_subset

end

end GafniTao
