import Dubon2026.RationalPrimeCyclotomicFiniteFactor
import Dubon2026.TameCyclicCharacterDescent
import Dubon2026.RationalPrimeFiniteTameGenerator
import Dubon2026.TameArtinianMatrixFactor

/-! The actual finite local restriction, containing prime-order roots,
supplies one tame presentation for both the Artinian deformation and the
fixed cyclotomic quotient. This discharges the full cyclotomic-kernel
condition needed by the auxiliary local deformation rings for Theorem 2.6.
The inertia exponent is the narrower input already supplied by the proved
regular tame diagonal-character classification. -/

namespace Dubon2026
noncomputable section
open Matrix

attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- An actual residual-unramified Artinian representation with the tame
inertia exponent descends uniquely through the actual prime cyclotomic
character. The finite stage must contain a primitive root; no abstract
cyclic quotient or cyclotomic-kernel premise is supplied. -/
theorem rationalPrime_artinian_cyclotomic_inertia_descent
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) [NeZero p]
    (q : ℕ) (hq : q.Prime) (hpq : p.Coprime q)
    {A ι F : Type} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [CharP (IsLocalRing.ResidueField A) q] [Fintype ι] [DecidableEq ι]
    [Field F] [NumberField F]
    (e : F →+* rationalPrimeLocalClosure p hp)
    (r : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →* Gal(F/ℚ))
    (he : ∀ g x, e (r g x) = g (e x))
    (ζ : F) (hζ : IsPrimitiveRoot (e ζ) p)
    (ρ : (Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker) →*
      GeneralLinearGroup ι A)
    (hres : ∀ g ∈ (rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker),
      GeneralLinearGroup.map (IsLocalRing.residue A) (ρ g) = 1)
    (hexp : ∀ g ∈ (rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker),
      ρ g ^ (p - 1) = 1) :
    ∃! θ : (ZMod p)ˣ →* GeneralLinearGroup ι A,
      ∀ g ∈ rationalPrimeNormInertia p hp,
        θ (rationalPrimeCyclotomicCharacter p hp p g) = ρ (QuotientGroup.mk' r.ker g) := by
  letI : Fact p.Prime := ⟨hp⟩
  let G := Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) ⧸ r.ker
  let I := (rationalPrimeNormInertia p hp).map (QuotientGroup.mk' r.ker)
  let π : G →* (ZMod p)ˣ := QuotientGroup.lift r.ker
    (rationalPrimeCyclotomicCharacter p hp p).toMonoidHom
    (rationalPrimeCyclotomicCharacter_kernel_of_embedded_root p hp p e r he ζ hζ)
  obtain ⟨φ, t, W, hW, ht, hWp, hWI, hgen, _, _⟩ :=
    rationalPrime_exists_finite_tame_generator p hp e r he
  letI := hW
  have hWρ : W ≤ ρ.ker := artinian_residual_unramified_kills_wild p q hq hpq I W hWI hWp ρ hres
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hWπ : W ≤ π.ker := by
    intro w hw
    obtain ⟨a, ha⟩ := hWp ⟨w, hw⟩
    have hpw : π w ^ (p ^ a) = 1 := by
      rw [← map_pow]
      exact (congrArg π (congrArg Subtype.val ha)).trans (map_one π)
    have hc : p.Coprime (p - 1) := (Nat.coprime_self_sub_right hp.one_lt.le).mpr (Nat.coprime_one_right p)
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (hc.pow_left a) (orderOf_dvd_of_pow_eq_one hpw)
    rw [← hcard]
    exact orderOf_dvd_natCard _
  have hπ : I.map π = ⊤ := by
    apply top_unique
    intro u _
    obtain ⟨g, hg, hu⟩ := rationalPrimeCyclotomicCharacter_inertia_surjective p hp hp2 u
    exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' r.ker g,
      Subgroup.mem_map.mpr ⟨g, hg, rfl⟩, hu⟩
  have htp : ρ t ^ Nat.card (ZMod p)ˣ = 1 := by rw [hcard]; exact hexp t ht
  obtain ⟨θ, hθ, huniq⟩ := tame_cyclic_quotient_unique_factor I W t hgen ρ π hWρ hWπ hπ htp
  refine ⟨θ, ?_, ?_⟩
  · intro g hg
    exact DFunLike.congr_fun hθ ⟨QuotientGroup.mk' r.ker g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩
  · intro ψ hψ
    apply huniq ψ
    apply MonoidHom.ext
    intro x
    obtain ⟨g, hg, hx⟩ := x.property
    change ψ (π x.val) = ρ x.val
    rw [← hx]
    exact hψ g hg

end
end Dubon2026
