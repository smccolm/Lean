import Dubon2026.OriginalInternalHomScalarExact
import Dubon2026.FiniteFirstCohomologySylowDetection

/-! # Integral H1 vanishing from original prime divisibility

The actual scalar map induces literal prime multiplication on H1. The
exact reduction sequence gives prime divisibility, while the existing
original finite-group theorem annihilates H1 by the group order. For a
p-group these force zero, the final integral lifting step needed for
the actual fundamental kernel's projectivity on DUB-17's duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- The actual integral scalar map induces literal natural-number multiplication on original first cohomology. -/
theorem originalScalarMultiplication_first_map
    {G : Type} [Group G] (A : Rep.{0} ℤ G) (p : ℕ) :
    (groupCohomology.functor ℤ G 1).map (originalScalarMultiplication A (p : ℤ)) =
      p • 𝟙 (groupCohomology A 1) := by
  have he : originalScalarMultiplication A (p : ℤ) = p • 𝟙 A := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (originalScalarMultiplication A (p : ℤ)).hom x = (p • 𝟙 A).hom x
    rw [originalScalarMultiplication_apply, Rep.nsmul_hom]
    exact Nat.cast_smul_eq_nsmul ℤ p x
  rw [he, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

/-- Prime divisibility of original H1 for a finite p-group forces vanishing, using the already proved group-order annihilation theorem. -/
theorem originalPGroup_first_cohomology_zero_of_prime_divisibility
    {G : Type} [Group G] [Fintype G] (A : Rep.{0} ℤ G)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (hp : ∀ x : groupCohomology A 1, ∃ y : groupCohomology A 1, p • y = x) :
    Limits.IsZero (groupCohomology A 1) := by
  have hpow (n : ℕ) : ∀ x : groupCohomology A 1,
      ∃ y : groupCohomology A 1, p ^ n • y = x := by
    induction n with
    | zero => intro x; exact ⟨x, one_nsmul x⟩
    | succ n ih =>
      intro x
      obtain ⟨y, hy⟩ := hp x
      obtain ⟨z, hz⟩ := ih y
      exact ⟨z, by rw [pow_succ, mul_nsmul, hz, hy]⟩
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  have hcard : Fintype.card G = p ^ n := by simpa only [Nat.card_eq_fintype_card] using hn
  have hz (x : groupCohomology A 1) : x = 0 := by
    obtain ⟨y, hy⟩ := hpow n x
    have hc := finiteFirstCohomology_card_nsmul_eq_zero A y
    rw [hcard, hy] at hc
    exact hc
  letI : Subsingleton (groupCohomology A 1) := ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- Zero first cohomology of the actual reduced internal Hom makes the original internal-Hom H1 prime-divisible through the genuine reduction sequence. -/
theorem originalInternalHom_first_prime_divisible
    {G : Type} [Group G] (A R : Rep.{0} ℤ G)
    [Module.Projective ℤ A] [Module.IsTorsionFree ℤ R] (p : ℕ) (hp : (p : ℤ) ≠ 0)
    (hred : Limits.IsZero (groupCohomology
      ((Rep.ihom (originalScalarReduction A (p : ℤ))).obj (originalScalarReduction R (p : ℤ))) 1)) :
    ∀ x : groupCohomology ((Rep.ihom A).obj R) 1,
      ∃ y : groupCohomology ((Rep.ihom A).obj R) 1, p • y = x := by
  have hX := originalInternalHomReduction_shortExact A R (p : ℤ) hp
  have he := (groupCohomology.mapShortComplex₂_exact hX 1).epi_f (hred.eq_zero_of_tgt _)
  have hs := (ModuleCat.epi_iff_surjective _).mp he
  intro x
  obtain ⟨y, hy⟩ := hs x
  refine ⟨y, ?_⟩
  change ((groupCohomology.functor ℤ G 1).map
    (originalScalarMultiplication ((Rep.ihom A).obj R) (p : ℤ))) y = x at hy
  rw [originalScalarMultiplication_first_map] at hy
  exact hy

end
end Dubon2026
