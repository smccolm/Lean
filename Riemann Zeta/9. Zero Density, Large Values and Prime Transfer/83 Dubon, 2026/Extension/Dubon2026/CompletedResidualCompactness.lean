import Dubon2026.CompletedResidualTopology
import Dubon2026.CompletedResidualFiniteQuotients
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-! # Compactness from the original finite residual power quotients -/

namespace Dubon2026

noncomputable section
open Matrix Filter Set
open scoped Topology Pointwise

variable {R : Type*} [CommRing R] [WithIdeal R]

/-- Actual finite ideal-power quotients supply finite covers for every adic neighborhood. -/
theorem adic_totallyBounded_of_finite_quotients
    (hfin : ∀ n : ℕ, Finite (R ⧸ (WithIdeal.i : Ideal R) ^ n)) :
    TotallyBounded (Set.univ : Set R) := by
  apply totallyBounded_iff_subset_finite_iUnion_nhds_zero.mpr
  intro U hU
  obtain ⟨n, _, hn⟩ :=
    (IsAdic.hasBasis_nhds_zero (I := (WithIdeal.i : Ideal R)) rfl).mem_iff.mp hU
  let J : Ideal R := (WithIdeal.i : Ideal R) ^ n
  letI : Finite (R ⧸ J) := hfin n
  let repr : R ⧸ J → R := fun q => Classical.choose (Ideal.Quotient.mk_surjective q)
  have hrepr (q : R ⧸ J) : Ideal.Quotient.mk J (repr q) = q :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective q)
  refine ⟨Set.range repr, Set.finite_range repr, ?_⟩
  intro x _
  apply Set.mem_iUnion.mpr
  refine ⟨repr (Ideal.Quotient.mk J x), Set.mem_iUnion.mpr ⟨Set.mem_range_self _, ?_⟩⟩
  have hx : x - repr (Ideal.Quotient.mk J x) ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hrepr, sub_self]
  change x ∈ (fun z : R => repr (Ideal.Quotient.mk J x) + z) '' U
  exact ⟨x - repr (Ideal.Quotient.mk J x), hn hx, by abel_nf⟩

/-- A complete actual adic ring with finite original power quotients is compact. -/
theorem adic_compactSpace_of_finite_quotients [CompleteSpace R]
    (hfin : ∀ n : ℕ, Finite (R ⧸ (WithIdeal.i : Ideal R) ^ n)) : CompactSpace R :=
  ⟨(adic_totallyBounded_of_finite_quotients hfin).isCompact_of_isClosed isClosed_univ⟩

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]

/-- The genuine original residual completion is compact in its actual maximal-adic topology when its original residue field is finite. -/
theorem residualRepresentationCompletion_compactSpace
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    CompactSpace (ResidualRepresentationCompletion ρ) :=
  adic_compactSpace_of_finite_quotients (residualRepresentationCompletion_finite_quotient ρ)

end
end Dubon2026
