import Dubon2026.SourceSemilinearCohomology
import Dubon2026.SourceParabolicClassification

/-! DUB17/18 -> original all-weight association -> original finite
Gamma1 character on parabolic H1. Retain the native cocycle quotient
and the original matrix representation. A parabolic cocycle is locally
a coboundary at each squared-trace-four element. This exact submodule
will receive the original cusp-period class and its coefficient changes;
character descent to its finite image remains a separate obligation. -/
namespace Dubon2026
noncomputable section
open groupCohomology
open scoped MatrixGroups
variable {R : Type} [CommRing R] (Γ : Subgroup SL(2, ℤ)) (A : Rep R Γ)

/-- Native cocycles that are coboundaries on every parabolic cyclic subgroup. -/
def sourceParabolicCocycles : Submodule R (cocycles₁ A) where
  carrier := {c | ∀ γ : Γ, γ.val.val.trace ^ 2 = 4 →
    ∃ v : A, c γ = A.ρ γ v - v}
  zero_mem' := fun γ _ => ⟨0, by change 0 = A.ρ γ 0 - 0; simp⟩
  add_mem' := by
    intro c d hc hd γ hγ
    obtain ⟨v, hv⟩ := hc γ hγ
    obtain ⟨w, hw⟩ := hd γ hγ
    refine ⟨v + w, ?_⟩
    change c γ + d γ = _
    rw [hv, hw, map_add]
    abel
  smul_mem' := by
    intro r c hc γ hγ
    obtain ⟨v, hv⟩ := hc γ hγ
    refine ⟨r • v, ?_⟩
    change r • c γ = _
    rw [hv, smul_sub, map_smul]

/-- The actual image of parabolic cocycles in native first cohomology. -/
def sourceParabolicH1 : Submodule R (H1 A) :=
  (sourceParabolicCocycles Γ A).map (H1π A).hom

theorem sourceParabolicH1_cocycle_iff (c : cocycles₁ A) :
    H1π A c ∈ sourceParabolicH1 Γ A ↔ c ∈ sourceParabolicCocycles Γ A := by
  constructor
  · rintro ⟨d, hd, he⟩
    obtain ⟨v, hv⟩ := (H1π_eq_iff d c).mp he
    intro γ hγ
    obtain ⟨w, hw⟩ := hd γ hγ
    refine ⟨w - v, ?_⟩
    have h := congrFun hv γ
    change A.ρ γ v - v = d γ - c γ at h
    rw [hw] at h
    calc
      c γ = (A.ρ γ w - w) - (A.ρ γ v - v) := by rw [h]; abel
      _ = A.ρ γ (w - v) - (w - v) := by rw [map_sub]; abel
  · intro hc
    exact ⟨c, hc, rfl⟩

variable {S : Type} [CommRing S] (B : Rep S Γ)
  (φ : R →+* S) (L : A →ₛₗ[φ] B)
  (hL : ∀ (g : Γ) (x : A), L (A.ρ g x) = B.ρ g (L x))

theorem sourceParabolicCocycles_semilinear
    {c : cocycles₁ A} (hc : c ∈ sourceParabolicCocycles Γ A) :
    sourceSemilinearCocycles A B φ L hL c ∈ sourceParabolicCocycles Γ B := by
  intro γ hγ
  obtain ⟨v, hv⟩ := hc γ hγ
  refine ⟨L v, ?_⟩
  rw [sourceSemilinearCocycles_apply, hv, map_sub, hL]

theorem sourceParabolicH1_semilinear
    {x : H1 A} (hx : x ∈ sourceParabolicH1 Γ A) :
    sourceSemilinearH1 A B φ L hL x ∈ sourceParabolicH1 Γ B := by
  obtain ⟨c, hc, rfl⟩ := hx
  rw [sourceSemilinearH1_cocycle]
  exact (sourceParabolicH1_cocycle_iff Γ B _).mpr
    (sourceParabolicCocycles_semilinear Γ A B φ L hL hc)

end
end Dubon2026
