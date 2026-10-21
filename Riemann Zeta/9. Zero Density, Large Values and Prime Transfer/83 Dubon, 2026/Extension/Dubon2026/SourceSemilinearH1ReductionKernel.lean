import Dubon2026.SourceSemilinearCohomology

/-! The kernel of native H1 coefficient reduction consists of scalar multiples.
DUB-17/18 -> residual modular Galois association -> nonzero residual binary
H1 eigensystem -> injective tensor coefficient change -> the prime-reduction kernel.

Adapted to native cohomology from anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_exists_coeffH1_map_ringHom_binaryFormRepSL.lean,
exists_eq_smul_of_H1map_eq_zero (Apache-2.0; retained LICENSE and NOTICE).
-/

namespace Dubon2026
noncomputable section

variable {R S G : Type} [CommRing R] [CommRing S] [Group G]
    (A : Rep R G) (B : Rep S G) (φ : R →+* S) (L : A →ₛₗ[φ] B)
    (hL : ∀ (g : G) (x : A), L (A.ρ g x) = B.ρ g (L x))

/-- For a surjective coefficient map with regular principal kernel, every class
killed by native H1 coefficient change is divisible by the original scalar. -/
theorem sourceSemilinearH1_exists_smul_of_zero (π : R)
    (hsurj : Function.Surjective L)
    (hdiv : ∀ x : A, L x = 0 → ∃ y : A, π • y = x)
    (hreg : Function.Injective (fun x : A => π • x))
    (x : groupCohomology.H1 A) (hx : sourceSemilinearH1 A B φ L hL x = 0) :
    ∃ y : groupCohomology.H1 A, x = π • y := by
  classical
  induction x using groupCohomology.H1_induction_on with
  | h z =>
    rw [sourceSemilinearH1_cocycle, groupCohomology.H1π_eq_zero_iff] at hx
    obtain ⟨vbar, hvbar⟩ := hx
    obtain ⟨v, rfl⟩ := hsurj vbar
    let b : groupCohomology.cocycles₁ A :=
      ⟨groupCohomology.d₀₁ A v, groupCohomology.d₀₁_apply_mem_cocycles₁ v⟩
    let u := z - b
    have hu0 (g : G) : L (u g) = 0 := by
      change L (z g - (A.ρ g v - v)) = 0
      rw [map_sub, map_sub, hL]
      have hg : B.ρ g (L v) - L v = L (z g) := congrFun hvbar g
      rw [hg, sub_self]
    choose w hw using fun g => hdiv (u g) (hu0 g)
    have hwc : w ∈ groupCohomology.cocycles₁ A := by
      apply (groupCohomology.mem_cocycles₁_iff _).mpr
      intro g h
      apply hreg
      change π • w (g * h) = π • (A.ρ g (w h) + w g)
      rw [smul_add, ← map_smul, hw, hw, hw]
      exact (groupCohomology.mem_cocycles₁_iff u).mp u.property g h
    let c : groupCohomology.cocycles₁ A := ⟨w, hwc⟩
    refine ⟨groupCohomology.H1π A c, ?_⟩
    rw [← map_smul, groupCohomology.H1π_eq_iff]
    refine ⟨v, ?_⟩
    funext g
    change A.ρ g v - v = z g - π • w g
    rw [hw]
    change A.ρ g v - v = z g - (z g - (A.ρ g v - v))
    abel

end
end Dubon2026
