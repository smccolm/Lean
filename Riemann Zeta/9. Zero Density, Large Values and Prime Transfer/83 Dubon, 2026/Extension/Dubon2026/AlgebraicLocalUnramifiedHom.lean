import Dubon2026.AlgebraicLocalInertiaCyclicity
import Dubon2026.AlgebraicLocalInertiaDepth
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Unramified finite representations on the original local Galois group
are constructed from their actual Frobenius image. Cyclicity and depth
are already proved in this repository; pinned Mathlib constructs the
finite cyclic homomorphism. This is the needed existence and uniqueness
input for DUB-17's unramified local deformation-ring description. -/

namespace Dubon2026
noncomputable section

variable (K L : Type) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [IsGalois K L] [Finite (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))]

attribute [local instance] algebraicLocalIntegerAction algebraicLocalIntegerBaseAlgebra

variable (φ : Gal(L/K))
  (hφ : ∀ x : algebraicLocalIntegerRing L,
    IsLocalRing.residue _ (φ • x) = (IsLocalRing.residue _ x) ^
      Nat.card (IsLocalRing.ResidueField (algebraicLocalIntegerRing K)))

include hφ

/-- Every element of a finite target is the actual Frobenius image of
an original continuous representation trivial on actual local inertia. -/
theorem algebraicLocal_exists_unramified_finite_hom
    [IsSepClosed L] [CharZero L]
    (T : Type) [Group T] [Finite T] [TopologicalSpace T] (t : T) :
    ∃ f : Gal(L/K) →ₜ* T, algebraicLocalInertia K L ≤ f.toMonoidHom.ker ∧ f φ = t := by
  obtain ⟨U, hU⟩ := algebraicLocal_exists_frobenius_depth K L φ hφ
    (orderOf t) (orderOf_pos t)
  let N := algebraicLocalInertia K L ⊔ U.toSubgroup
  let π := QuotientGroup.mk' N
  have hgen : ∀ x : Gal(L/K) ⧸ N, x ∈ Subgroup.zpowers (π φ) :=
    algebraicLocal_frobenius_generates_inertia_quotient K L φ hφ U
  have hd : orderOf t ∣ orderOf (π φ) := by
    apply hU
    apply (QuotientGroup.eq_one_iff _).mp
    change π (φ ^ orderOf (π φ)) = 1
    rw [map_pow, pow_orderOf_eq_one]
  let ψ := monoidHomOfForallMemZpowers hgen hd
  have hopen : IsOpen (N : Set Gal(L/K)) := Subgroup.isOpen_mono le_sup_right U.isOpen
  letI : DiscreteTopology (Gal(L/K) ⧸ N) := QuotientGroup.discreteTopology hopen
  have hπ : Continuous π := continuous_quot_mk
  have hψ : Continuous ψ := continuous_of_discreteTopology
  let f : Gal(L/K) →ₜ* T := ⟨ψ.comp π, hψ.comp hπ⟩
  refine ⟨f, ?_, ?_⟩
  · intro g hg
    change ψ (π g) = 1
    have he : π g = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left hg)
    rw [he, map_one]
  · exact monoidHomOfForallMemZpowers_apply_gen hgen hd

/-- Original continuous unramified representations into a discrete target
are determined by their image of the same actual residue Frobenius. -/
theorem algebraicLocal_unramified_hom_ext
    {T : Type} [Group T] [TopologicalSpace T] [DiscreteTopology T]
    (f g : Gal(L/K) →ₜ* T)
    (hf : algebraicLocalInertia K L ≤ f.toMonoidHom.ker)
    (hg : algebraicLocalInertia K L ≤ g.toMonoidHom.ker)
    (he : f φ = g φ) : f = g := by
  let U : OpenNormalSubgroup Gal(L/K) := {
    toOpenSubgroup := ⟨f.toMonoidHom.ker ⊓ g.toMonoidHom.ker,
      ((isOpen_discrete ({1} : Set T)).preimage f.continuous).inter
        ((isOpen_discrete ({1} : Set T)).preimage g.continuous)⟩
    isNormal' := inferInstance }
  let N := algebraicLocalInertia K L ⊔ U.toSubgroup
  let π := QuotientGroup.mk' N
  let fbar := QuotientGroup.lift N f.toMonoidHom (sup_le hf inf_le_left)
  let gbar := QuotientGroup.lift N g.toMonoidHom (sup_le hg inf_le_right)
  have hgen : ∀ x : Gal(L/K) ⧸ N, x ∈ Subgroup.zpowers (π φ) :=
    algebraicLocal_frobenius_generates_inertia_quotient K L φ hφ U
  have hfg : fbar = gbar := (MonoidHom.eq_iff_eq_on_generator hgen fbar gbar).mpr he
  ext x
  exact DFunLike.congr_fun hfg (π x)

end
end Dubon2026
