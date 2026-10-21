import Dubon2026.SourceHeckeCohomologyTrace
import Dubon2026.CosetTraceRepresentativeChange

/-! Degree-one representative independence for the original finite coset trace.
DUB-17/18 -> residual modular Galois association -> residual H1 eigensystem
-> full H1 Hecke commutativity -> reindexing the composed trace by actual
product representatives. The degree-two comparison already in the repository
does not supply this degree-one statement; the native one-cocycle identity
gives its exact zero-cochain witness.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
    (S : Subgroup G) (a : G ⧸ S → S)

/-- A literal degree-one trace summand after changing each original representative by a subgroup element. -/
def sourceChangedCosetTraceOneTerm (c : S → A) (g : G) (q : G ⧸ S) : A :=
  A.ρ (g • q).out (A.ρ (a (g • q)) (c (changedCosetTransition S a g q)))

/-- The one-cocycle identity gives the exact representative correction for each genuine trace summand. -/
theorem sourceChangedCosetTraceOneTerm_sub
    (c : groupCohomology.cocycles₁ (restrictedCoefficientRep A S.subtype))
    (g : G) (q : G ⧸ S) :
    sourceChangedCosetTraceOneTerm A S a c g q - cosetTraceOneTerm A S c g q =
      A.ρ g (A.ρ q.out (c (a q))) - A.ρ (g • q).out (c (a (g • q))) := by
  have h₁ := (groupCohomology.mem_cocycles₁_iff _).mp c.property
    (a (g • q)) (changedCosetTransition S a g q)
  have h₂ := (groupCohomology.mem_cocycles₁_iff _).mp c.property
    (cosetTransition S g q) (a q)
  have he : a (g • q) * changedCosetTransition S a g q = cosetTransition S g q * a q := by
    simp only [changedCosetTransition]
    group
  rw [he] at h₁
  have hterm : A.ρ (a (g • q)) (c (changedCosetTransition S a g q)) -
      c (cosetTransition S g q) =
      A.ρ (cosetTransition S g q) (c (a q)) - c (a (g • q)) := by
    change c _ = A.ρ (a (g • q)) (c _) + c _ at h₁
    change c _ = A.ρ (cosetTransition S g q) (c _) + c _ at h₂
    rw [h₂] at h₁
    exact sub_eq_sub_iff_add_eq_add.mpr h₁.symm
  have h := congrArg (A.ρ (g • q).out) hterm
  rw [map_sub, map_sub, cosetTransition_action] at h
  exact h

variable [Fintype (G ⧸ S)]

/-- The full literal degree-one trace with changed coset representatives. -/
def sourceChangedCosetTraceOne (c : S → A) (g : G) : A :=
  ∑ q : G ⧸ S, sourceChangedCosetTraceOneTerm A S a c g q

/-- The changed original trace differs by the actual coboundary of the explicit
sum of correction values, so its native H1 class is unchanged. -/
theorem sourceChangedCosetTraceOne_sub
    (c : groupCohomology.cocycles₁ (restrictedCoefficientRep A S.subtype)) :
    sourceChangedCosetTraceOne A S a c - cosetTraceOne A S c =
      groupCohomology.d₀₁ A (∑ q : G ⧸ S, A.ρ q.out (c (a q))) := by
  funext g
  change (∑ q, sourceChangedCosetTraceOneTerm A S a c g q) -
      (∑ q, cosetTraceOneTerm A S c g q) =
      A.ρ g (∑ q, A.ρ q.out (c (a q))) - ∑ q, A.ρ q.out (c (a q))
  rw [← Finset.sum_sub_distrib]
  simp_rw [sourceChangedCosetTraceOneTerm_sub]
  rw [Finset.sum_sub_distrib, ← map_sum]
  have he := Equiv.sum_comp (MulAction.toPerm g)
    (fun q : G ⧸ S => A.ρ q.out (c (a q)))
  change (∑ q, A.ρ (g • q).out (c (a (g • q)))) = _ at he
  rw [he]

end
end Dubon2026
