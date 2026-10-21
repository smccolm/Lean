import Dubon2026.SourceChosenCosetTraceOne

/-! The native degree-one correspondence and its representative comparison.
DUB-17/18 -> residual modular Galois association -> original residual H1
eigensystem -> full H1 Hecke commutativity -> the product correspondence.
This factors the actual finite trace, retaining its literal coefficient map.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
    (S : Subgroup G) [Fintype (G ⧸ S)] (θ : S →* G) (b : Module.End R A)

/-- The literal coefficient pullback for the original finite correspondence. -/
def sourceCorrespondencePull : (G → A) →ₗ[R] (S → A) where
  toFun c u := b (c (θ u))
  map_add' c d := by ext u; exact map_add b _ _
  map_smul' r c := by ext u; exact map_smul b r _

/-- The literal full degree-one finite correspondence on cochains. -/
def sourceCorrespondenceOne : (G → A) →ₗ[R] (G → A) :=
  (cosetTraceOne A S).comp (sourceCorrespondencePull A S θ b)

/-- The actual finite correspondence retains every original trace summand. -/
theorem sourceCorrespondenceOne_apply (c : G → A) (g : G) :
    sourceCorrespondenceOne A S θ b c g =
      ∑ q : G ⧸ S, A.ρ (g • q).out (b (c (θ (cosetTransition S g q)))) := rfl

variable (hb : ∀ u : S, b.comp (A.ρ (θ u)) = (A.ρ u.val).comp b)

include hb

omit [Fintype (G ⧸ S)] in
/-- The equivariant coefficient pullback is an actual subgroup one-cocycle. -/
theorem sourceCorrespondencePull_mem
    (c : groupCohomology.cocycles₁ A) :
    sourceCorrespondencePull A S θ b c ∈
      groupCohomology.cocycles₁ (restrictedCoefficientRep A S.subtype) := by
  apply (groupCohomology.mem_cocycles₁_iff _).mpr
  intro g h
  change b (c (θ (g * h))) = A.ρ g.val (b (c (θ h))) + b (c (θ g))
  have hc := (groupCohomology.mem_cocycles₁_iff _).mp c.property (θ g) (θ h)
  change c (θ g * θ h) = A.ρ (θ g) (c (θ h)) + c (θ g) at hc
  rw [map_mul, hc, map_add]
  rw [show b (A.ρ (θ g) (c (θ h))) = A.ρ g.val (b (c (θ h))) from
    LinearMap.congr_fun (hb g) _]

/-- The actual finite correspondence takes native one-cocycles to native one-cocycles. -/
theorem sourceCorrespondenceOne_mem
    (c : groupCohomology.cocycles₁ A) :
    sourceCorrespondenceOne A S θ b c ∈ groupCohomology.cocycles₁ A :=
  cosetTraceOne_mem_cocycles A S
    ⟨_, sourceCorrespondencePull_mem A S θ b hb c⟩

/-- The actual finite correspondence preserves the original native coboundaries. -/
theorem sourceCorrespondenceOne_coboundary {c : G → A}
    (hc : c ∈ groupCohomology.coboundaries₁ A) :
    sourceCorrespondenceOne A S θ b c ∈ groupCohomology.coboundaries₁ A := by
  obtain ⟨v, rfl⟩ := hc
  have he : sourceCorrespondencePull A S θ b (groupCohomology.d₀₁ A v) =
      groupCohomology.d₀₁ (restrictedCoefficientRep A S.subtype) (b v) := by
    funext u
    change b (A.ρ (θ u) v - v) = A.ρ u.val (b v) - b v
    rw [map_sub, show b (A.ρ (θ u) v) = A.ρ u.val (b v) from
      LinearMap.congr_fun (hb u) v]
  change cosetTraceOne A S (sourceCorrespondencePull A S θ b _) ∈ _
  rw [he, cosetTraceOne_coboundary]
  exact LinearMap.mem_range_self _ _

/-- Changing genuine representatives in the full correspondence alters its value
only by a proved native coboundary. -/
theorem sourceCorrespondenceOne_chosen_sub
    (s : G ⧸ S → G) (hs : ∀ q, (s q : G ⧸ S) = q)
    (c : groupCohomology.cocycles₁ A) :
    (fun g => ∑ q : G ⧸ S,
      A.ρ (s (g • q)) (b (c (θ (sourceChosenCosetTransition S s hs g q))))) -
      sourceCorrespondenceOne A S θ b c ∈ groupCohomology.coboundaries₁ A :=
  sourceChosenCosetTraceOne_sub A S s hs
    ⟨_, sourceCorrespondencePull_mem A S θ b hb c⟩

end
end Dubon2026
