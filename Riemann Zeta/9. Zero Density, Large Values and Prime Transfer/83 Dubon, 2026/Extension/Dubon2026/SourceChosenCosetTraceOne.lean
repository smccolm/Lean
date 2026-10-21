import Dubon2026.SourceHeckeTraceOneRepresentativeChange

/-! Arbitrary genuine representatives in the existing degree-one trace.
DUB-17/18 -> residual modular Galois association -> full residual H1
eigensystem -> Hecke commutativity -> product correspondence comparison.
The representative error is an explicit native coboundary.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
    (S : Subgroup G) [Fintype (G ⧸ S)]
    (s : G ⧸ S → G) (hs : ∀ q, (s q : G ⧸ S) = q)

/-- The actual transition belonging to any genuine choice of coset representatives. -/
def sourceChosenCosetTransition (g : G) (q : G ⧸ S) : S :=
  ⟨(s (g • q))⁻¹ * (g * s q), by
    apply QuotientGroup.eq.mp
    rw [hs]
    change g • q = g • (s q : G ⧸ S)
    rw [hs]⟩

private def representativeCorrection (q : G ⧸ S) : S :=
  ⟨q.out⁻¹ * s q, QuotientGroup.eq.mp (by rw [QuotientGroup.out_eq', hs])⟩

/-- The full trace with chosen genuine representatives differs from the original
trace by a native coboundary, with no representative-independence premise. -/
theorem sourceChosenCosetTraceOne_sub
    (c : groupCohomology.cocycles₁ (restrictedCoefficientRep A S.subtype)) :
    (fun g => ∑ q : G ⧸ S, A.ρ (s (g • q)) (c (sourceChosenCosetTransition S s hs g q))) -
      cosetTraceOne A S c ∈ groupCohomology.coboundaries₁ A := by
  let a := representativeCorrection S s hs
  have he (g : G) (q : G ⧸ S) :
      changedCosetTransition S a g q = sourceChosenCosetTransition S s hs g q := by
    apply Subtype.ext
    change ((g • q).out⁻¹ * s (g • q))⁻¹ *
      ((g • q).out⁻¹ * (g * q.out)) * (q.out⁻¹ * s q) = _
    change _ = (s (g • q))⁻¹ * (g * s q)
    group
  have ht : sourceChangedCosetTraceOne A S a c =
      fun g => ∑ q : G ⧸ S,
        A.ρ (s (g • q)) (c (sourceChosenCosetTransition S s hs g q)) := by
    funext g
    apply Finset.sum_congr rfl
    intro q _
    change A.ρ (g • q).out (A.ρ (a (g • q)) (c (changedCosetTransition S a g q))) = _
    rw [he, ← Module.End.mul_apply, ← map_mul]
    change A.ρ ((g • q).out * ((g • q).out⁻¹ * s (g • q))) _ = _
    rw [mul_inv_cancel_left]
  rw [← ht, sourceChangedCosetTraceOne_sub]
  exact LinearMap.mem_range_self _ _

end
end Dubon2026
