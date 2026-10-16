import Dubon2026.CosetTraceDifferential

/-! # Changing the representatives in the actual coset trace

The explicit coboundary below is the representative-independence input
for the local restriction/transfer comparison on DUB-17's reciprocity
and normalized finite class invariant dependency chain.
-/

namespace Dubon2026
noncomputable section
open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G]

/-- The cocycle identity gives the exact change under a change of three
transition representatives, before summing over any cosets. -/
theorem cocycleTwo_representative_change (A : Rep R G)
    (c : groupCohomology.cocycles₂ A) (x y z u v : G) :
    A.ρ x (c (x⁻¹ * u * y, y⁻¹ * v * z)) - c (u, v) =
      A.ρ u (c (y, y⁻¹ * v * z) - c (v, z)) +
        (c (x, x⁻¹ * u * y) - c (u, y)) -
        (c (x, x⁻¹ * (u * v) * z) - c (u * v, z)) := by
  have hc (g h j : G) : c (g * h, j) + c (g, h) = A.ρ g (c (h, j)) + c (g, h * j) :=
    (groupCohomology.mem_cocycles₂_iff _).mp c.property g h j
  have h₁ := hc x (x⁻¹ * u * y) (y⁻¹ * v * z)
  have h₂ := hc u y (y⁻¹ * v * z)
  have h₃ := hc u v z
  have hxy : x * (x⁻¹ * u * y) = u * y := by group
  have hyz : y * (y⁻¹ * v * z) = v * z := by group
  have hxyz : (x⁻¹ * u * y) * (y⁻¹ * v * z) = x⁻¹ * (u * v) * z := by group
  rw [hxy, hxyz] at h₁
  rw [hyz] at h₂
  have e₁ := eq_sub_of_add_eq h₁.symm
  have e₂ := eq_sub_of_add_eq h₂
  have e₃ : c (u, v * z) = c (u * v, z) + c (u, v) - A.ρ u (c (v, z)) :=
    eq_sub_of_add_eq ((add_comm _ _).trans h₃.symm)
  rw [e₁, e₂, e₃, map_sub]
  abel

variable (A : Rep R G) (S : Subgroup G)

/-- The transition inside the original subgroup after multiplying each
chosen coset representative on the right by an actual subgroup element. -/
def changedCosetTransition (a : G ⧸ S → S) (g : G) (q : G ⧸ S) : S :=
  (a (g • q))⁻¹ * cosetTransition S g q * a q

/-- One literal trace summand computed with the changed representatives. -/
def changedCosetTraceTwoTerm (a : G ⧸ S → S) (c : S × S → A)
    (g h : G) (q : G ⧸ S) : A :=
  A.ρ (g • h • q).out (A.ρ (a (g • h • q))
    (c (changedCosetTransition S a g (h • q), changedCosetTransition S a h q)))

/-- The explicit one-cochain term comparing the original and changed traces. -/
def cosetRepresentativeHomotopyTerm (a : G ⧸ S → S) (c : S × S → A)
    (g : G) (q : G ⧸ S) : A :=
  A.ρ (g • q).out
    (c (a (g • q), changedCosetTransition S a g q) - c (cosetTransition S g q, a q))

/-- The changed trace differs from the original trace by the explicit
differential term, with the same coset reindexing as the original trace. -/
theorem changedCosetTraceTwoTerm_sub (a : G ⧸ S → S)
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype))
    (g h : G) (q : G ⧸ S) :
    changedCosetTraceTwoTerm A S a c g h q - cosetTraceTwoTerm A S c g h q =
      A.ρ g (cosetRepresentativeHomotopyTerm A S a c h q) +
        cosetRepresentativeHomotopyTerm A S a c g (h • q) -
        cosetRepresentativeHomotopyTerm A S a c (g * h) q := by
  have hc := congrArg (A.ρ (g • h • q).out)
    (cocycleTwo_representative_change (restrictedCoefficientRep A S.subtype) c
      (a (g • h • q)) (a (h • q)) (a q)
      (cosetTransition S g (h • q)) (cosetTransition S h q))
  change A.ρ (g • h • q).out
      (A.ρ (a (g • h • q))
        (c (changedCosetTransition S a g (h • q), changedCosetTransition S a h q)) -
          c (cosetTransition S g (h • q), cosetTransition S h q)) = _ at hc
  rw [map_sub, map_sub, map_add] at hc
  change A.ρ (g • h • q).out
      (A.ρ (a (g • h • q))
        (c (changedCosetTransition S a g (h • q), changedCosetTransition S a h q))) -
      A.ρ (g • h • q).out (c (cosetTransition S g (h • q), cosetTransition S h q)) =
    A.ρ (g • h • q).out
        (A.ρ (cosetTransition S g (h • q))
          (c (a (h • q), (a (h • q))⁻¹ * cosetTransition S h q * a q) -
            c (cosetTransition S h q, a q))) + _ - _ at hc
  rw [cosetTransition_action] at hc
  simpa only [changedCosetTraceTwoTerm, cosetTraceTwoTerm,
    cosetRepresentativeHomotopyTerm, changedCosetTransition, cosetTransition_mul,
    mul_smul] using hc

variable [Fintype (G ⧸ S)]

/-- The genuine one-cochain witnessing representative independence. -/
def cosetRepresentativeHomotopy (a : G ⧸ S → S) (c : S × S → A) (g : G) : A :=
  ∑ q : G ⧸ S, cosetRepresentativeHomotopyTerm A S a c g q

/-- Summing the exact transition identity gives an actual coboundary,
so no representative choice can change the resulting transfer class. -/
theorem changedCosetTraceTwo_sub (a : G ⧸ S → S)
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype)) :
    (fun z : G × G => ∑ q : G ⧸ S, changedCosetTraceTwoTerm A S a c z.1 z.2 q) -
        cosetTraceTwo A S c = groupCohomology.d₁₂ A (cosetRepresentativeHomotopy A S a c) := by
  funext z
  obtain ⟨g, h⟩ := z
  change (∑ q, changedCosetTraceTwoTerm A S a c g h q) -
      (∑ q, cosetTraceTwoTerm A S c g h q) =
    A.ρ g (∑ q, cosetRepresentativeHomotopyTerm A S a c h q) -
      (∑ q, cosetRepresentativeHomotopyTerm A S a c (g * h) q) +
      (∑ q, cosetRepresentativeHomotopyTerm A S a c g q)
  rw [← Finset.sum_sub_distrib]
  simp_rw [changedCosetTraceTwoTerm_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, map_sum]
  have he := Equiv.sum_comp (MulAction.toPerm h)
    (fun q : G ⧸ S => cosetRepresentativeHomotopyTerm A S a c g q)
  change (∑ q, cosetRepresentativeHomotopyTerm A S a c g (h • q)) = _ at he
  rw [he]
  abel

end
end Dubon2026
