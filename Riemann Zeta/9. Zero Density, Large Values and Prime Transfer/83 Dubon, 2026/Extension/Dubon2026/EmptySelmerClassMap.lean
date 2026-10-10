import Dubon2026.SelmerRepresentativeIdealRoots

/-! # The actual empty-set Selmer class map on the original fractional ideals -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped nonZeroDivisors

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The literal class quotient of the original invertible fractional ideals. -/
abbrev OriginalFractionalIdealClassQuotient :=
  (FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range

/-- Original field-unit representatives project to their actual empty-set Selmer classes. -/
def emptySelmerRepresentativeProjection (n : ℕ) :
    EmptySelmerRepresentativeUnits (R := R) (K := K) n →*
      IsDedekindDomain.selmerGroup (R := R) (K := K) (S := ∅) (n := n) :=
  ((QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range).comp
    (EmptySelmerRepresentativeUnits (R := R) (K := K) n).subtype).codRestrict _
      (fun x => x.property)

/-- Every original empty-set Selmer class has a genuine field-unit representative. -/
theorem emptySelmerRepresentativeProjection_surjective (n : ℕ) :
    Function.Surjective (emptySelmerRepresentativeProjection (R := R) (K := K) n) := by
  intro z
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (powMonoidHom (α := Kˣ) n).range z.val
  have hmem : x ∈ EmptySelmerRepresentativeUnits (R := R) (K := K) n := by
    change QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range x ∈
      IsDedekindDomain.selmerGroup (R := R) (K := K) (S := ∅) (n := n)
    rw [hx]
    exact z.property
  exact ⟨⟨x, hmem⟩, Subtype.ext hx⟩

/-- Original Selmer representatives map to the class of their actual principal-ideal roots. -/
def emptySelmerRepresentativeClass (n : ℕ) (hn : n ≠ 0) :
    EmptySelmerRepresentativeUnits (R := R) (K := K) n →*
      OriginalFractionalIdealClassQuotient (R := R) (K := K) :=
  (QuotientGroup.mk' (toPrincipalIdeal R K).range).comp
    (emptySelmerRepresentativeIdealRootHom n hn)

/-- Changing an original Selmer representative by an nth power does not change its actual ideal-root class. -/
theorem emptySelmerRepresentativeProjection_kernel_le (n : ℕ) (hn : n ≠ 0) :
    (emptySelmerRepresentativeProjection (R := R) (K := K) n).ker ≤
      (emptySelmerRepresentativeClass n hn).ker := by
  intro x hx
  have hxq := congrArg Subtype.val hx
  change QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range x.val = 1 at hxq
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff x.val).mp hxq
  change QuotientGroup.mk' (toPrincipalIdeal R K).range
    (emptySelmerRepresentativeIdealRoot n x) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨y, ?_⟩
  exact (emptySelmerRepresentativeIdealRoot_of_power n hn x y hy.symm).symm

/-- The actual ideal-root class map descends to the original empty-set Selmer group. -/
def emptySelmerClassMap (n : ℕ) (hn : n ≠ 0) :
    IsDedekindDomain.selmerGroup (R := R) (K := K) (S := ∅) (n := n) →*
      OriginalFractionalIdealClassQuotient (R := R) (K := K) :=
  (emptySelmerRepresentativeProjection n).liftOfSurjective
    (emptySelmerRepresentativeProjection_surjective n)
    ⟨emptySelmerRepresentativeClass n hn, emptySelmerRepresentativeProjection_kernel_le n hn⟩

/-- The descended map retains the class of the actual root of every original principal ideal. -/
theorem emptySelmerClassMap_apply_representative (n : ℕ) (hn : n ≠ 0)
    (x : EmptySelmerRepresentativeUnits (R := R) (K := K) n) :
    emptySelmerClassMap n hn (emptySelmerRepresentativeProjection n x) =
      emptySelmerRepresentativeClass n hn x := by
  unfold emptySelmerClassMap
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- The original Selmer class map takes values in actual n-torsion ideal classes. -/
theorem emptySelmerClassMap_pow (n : ℕ) (hn : n ≠ 0)
    (z : IsDedekindDomain.selmerGroup (R := R) (K := K) (S := ∅) (n := n)) :
    emptySelmerClassMap n hn z ^ n = 1 := by
  obtain ⟨x, rfl⟩ := emptySelmerRepresentativeProjection_surjective n z
  rw [emptySelmerClassMap_apply_representative]
  change (QuotientGroup.mk' (toPrincipalIdeal R K).range
    (emptySelmerRepresentativeIdealRoot n x)) ^ n = 1
  rw [← map_pow, emptySelmerRepresentativeIdealRoot_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨x.val, rfl⟩

end
end Dubon2026
