import Dubon2026.ContinuousUnramifiedDimensionBound
import Dubon2026.ContinuousFiniteInflationUnramified
import Mathlib.RingTheory.Finiteness.Cardinality

/-! DUB-17's local unramified H1 dimension, conditional only on the
original local arithmetic cyclicity/depth and already available local H1
finiteness. The native continuous/inflation comparison, coefficient period
and finite-stage norm cancellation are derived. No external local-class
model or separately supplied norm-zero certificate is used. -/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {K G : Type} [Field K] [Group G]
  [TopologicalSpace K] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (A : Rep K G) [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul K A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (I : Subgroup G) [I.Normal]

omit [CompactSpace G] [I.Normal] in
/-- One sufficiently deep original cyclic quotient supplies the reverse
bound for the original continuous inertia kernel. -/
theorem invariants_finrank_le_continuous_unramified_of_deep_quotient
    [FiniteDimensional K A] [FiniteDimensional K (ContinuousRepresentationH1 A hA)]
    (N : Subgroup G) [N.Normal] [Fintype (G ⧸ N)]
    (hIN : I ≤ N) (hN : IsOpen (N : Set G))
    (p d : ℕ) [CharP K p] (g : G ⧸ N) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hperiod : (A.quotientToInvariants N).ρ g ^ d = 1)
    (hsize : p * d ∣ Fintype.card (G ⧸ N)) :
    Module.finrank K A.ρ.invariants ≤ Module.finrank K
      (continuousRepresentationH1Restriction A hA I.subtype continuous_subtype_val).ker := by
  let P := (continuousRepresentationH1Restriction A hA I.subtype continuous_subtype_val).ker
  letI : Module.Finite K P := Module.Finite.of_injective P.subtype P.subtype_injective
  let L : P →ₗ[K] groupCohomology A 1 := (continuousH1ToAlgebraic A hA).comp P.subtype
  letI : Module.Finite K L.range := Module.Finite.range L
  have hi : Function.Injective L :=
    (continuousH1ToAlgebraic_injective A hA).comp P.subtype_injective
  have hle := firstInflation_range_le_continuous_unramified_image A hA I N hIN hN
  have hr : L.range = P.map (continuousH1ToAlgebraic A hA) := by
    simp only [L, LinearMap.range_comp, Submodule.range_subtype]
  have hd := finite_cyclic_firstInflation_finrank_eq A N p d g hg hperiod hsize
  calc
    Module.finrank K A.ρ.invariants =
        Module.finrank K (groupCohomology.H1InfRes A N).f.hom.range := hd.symm
    _ ≤ Module.finrank K L.range := Submodule.finrank_mono (t := L.range) (by rwa [hr])
    _ = Module.finrank K P := LinearMap.finrank_range_of_inj hi

omit [TopologicalSpace K] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul K A] in
/-- A period of the original action is a period on every original
quotient-invariant coefficient space at the image of the same element. -/
theorem quotientInvariant_action_period (N : Subgroup G) [N.Normal]
    (φ : G) (d : ℕ) (hd : A.ρ φ ^ d = 1) :
    (A.quotientToInvariants N).ρ (QuotientGroup.mk φ) ^ d = 1 := by
  rw [← map_pow, ← QuotientGroup.mk_pow]
  ext x
  change A.ρ (φ ^ d) x.val = x.val
  rw [map_pow, hd]
  rfl

/-- For the original continuous representation over a finite field,
cyclic inertia quotients of arbitrarily divisible order give exactly the
global invariant dimension. All finite-stage and continuity witnesses
are constructed; actual arithmetic cyclicity and depth remain explicit. -/
theorem continuous_unramified_finrank_eq_invariants_of_cyclic_depth
    [Finite K] [FiniteDimensional K A]
    [FiniteDimensional K (ContinuousRepresentationH1 A hA)]
    (p : ℕ) [Fact p.Prime] [CharP K p] (φ : G)
    (hcyclic : ∀ U : OpenNormalSubgroup G, ∀ x : G ⧸ (I ⊔ U.toSubgroup),
      x ∈ Subgroup.zpowers (QuotientGroup.mk φ))
    (hdepth : ∀ n : ℕ, 0 < n → ∃ U : OpenNormalSubgroup G,
      n ∣ Nat.card (G ⧸ (I ⊔ U.toSubgroup))) :
    Module.finrank K (continuousRepresentationH1Restriction A hA
      I.subtype continuous_subtype_val).ker = Module.finrank K A.ρ.invariants := by
  apply Nat.le_antisymm
  · exact continuous_unramified_finrank_le_invariants A hA I
      (fun U => ⟨⟨QuotientGroup.mk φ, hcyclic U⟩⟩)
  · letI : Finite A := Module.finite_of_finite K
    letI : Finite (Module.End K A) :=
      Finite.of_injective (fun f : Module.End K A => (f : A → A)) DFunLike.coe_injective
    letI : Finite (Module.End K A)ˣ := Finite.of_injective Units.val Units.val_injective
    let d := Nat.card (Module.End K A)ˣ
    have hdpos : 0 < d := Nat.card_pos
    have hperiod : A.ρ φ ^ d = 1 := by
      have h := pow_card_eq_one' (x := A.ρ.asGroupHom φ)
      exact congrArg Units.val h
    obtain ⟨U, hU⟩ := hdepth (p * d) (Nat.mul_pos (Fact.out : p.Prime).pos hdpos)
    let N := I ⊔ U.toSubgroup
    have hN : IsOpen (N : Set G) := Subgroup.isOpen_mono le_sup_right U.isOpen
    letI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
    letI : Fintype (G ⧸ N) := Fintype.ofFinite _
    apply invariants_finrank_le_continuous_unramified_of_deep_quotient A hA I N
      le_sup_left hN p d (QuotientGroup.mk φ) (hcyclic U)
      (quotientInvariant_action_period A N φ d hperiod)
    simpa only [Nat.card_eq_fintype_card] using hU

end
end Dubon2026
