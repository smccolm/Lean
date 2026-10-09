import Dubon2026.LocalInducedHeckeValues
import Dubon2026.FinitePlaceHeckeTrace

/-! # The genuine intrinsic Hecke eigenvalue of the actual spherical induced vector -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

private theorem induced_finite_sum_eval {G ι : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Fintype ι] (B : Subgroup G) (χ : B →* ℂ)
    (a : ι → G) (f : smoothInducedCharacterSpace B χ) (g : G) :
    ((∑ i, smoothInducedCharacterRepresentation B χ (a i)) f).val g =
      ∑ i, f.val (g * a i) := by
  let ev : smoothInducedCharacterSpace B χ →ₗ[ℂ] ℂ :=
    (LinearMap.proj g).comp (smoothInducedCharacterSpace B χ).subtype
  have he := map_sum ev (fun i => smoothInducedCharacterRepresentation B χ (a i) f) Finset.univ
  simpa only [LinearMap.sum_apply] using he

/-- The actual intrinsic Hecke sum at the identity has its exact original unnormalized inducing value. -/
theorem finitePlaceInducedSpherical_hecke_identity (p : ℕ) [NeZero p] [Fact p.Prime]
    (z₁ z₂ : ℂˣ) :
    (finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p)
      (smoothInducedCharacterRepresentation _
        (finitePlaceLowerCharacter (rationalPrimePlace p (Fact.out : p.Prime)) z₁ z₂))
      (finitePlaceInducedSpherical (rationalPrimePlace p (Fact.out : p.Prime)) z₁ z₂)).val 1 =
      (p : ℂ) * (z₁⁻¹ : ℂˣ) + (z₂⁻¹ : ℂˣ) := by
  let v := rationalPrimePlace p (Fact.out : p.Prime)
  let f := finitePlaceInducedSpherical v z₁ z₂
  have hsome (a : ZMod p) :
      f.val ((finitePlaceHeckeGamma 1 p (Nat.coprime_one_right p) v (some a))⁻¹ *
        (GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p))⁻¹) =
      if a = 0 then ((z₂⁻¹ : ℂˣ) : ℂ) else (z₁⁻¹ : ℂˣ) := by
    by_cases ha : a = 0
    · subst a
      simpa only [if_pos rfl] using finitePlaceInducedSpherical_hecke_zero p Fact.out z₁ z₂
    · simpa only [if_neg ha] using finitePlaceInducedSpherical_hecke_nonzero p Fact.out z₁ z₂ a ha
  rw [finitePlaceHeckeTrace, induced_finite_sum_eval]
  simp only [one_mul, map_mul, map_inv]
  change (∑ i : Option (ZMod p), f.val
    ((finitePlaceHeckeGamma 1 p (Nat.coprime_one_right p) v i)⁻¹ *
      (GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p))⁻¹)) = _
  rw [Fintype.sum_option, finitePlaceInducedSpherical_hecke_none p Fact.out z₁ z₂]
  simp_rw [hsome]
  have he (a : ZMod p) : (if a = 0 then ((z₂⁻¹ : ℂˣ) : ℂ) else (z₁⁻¹ : ℂˣ)) =
      (z₁⁻¹ : ℂˣ) + if a = 0 then ((z₂⁻¹ : ℂˣ) : ℂ) - (z₁⁻¹ : ℂˣ) else 0 := by
    split_ifs <;> ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The original induced spherical section is a genuine eigenvector of the actual intrinsic local Hecke operator, with its literal two-parameter eigenvalue. -/
theorem finitePlaceInducedSpherical_hecke_eigenvalue (p : ℕ) [NeZero p] [Fact p.Prime]
    (z₁ z₂ : ℂˣ) :
    finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p)
      (smoothInducedCharacterRepresentation _
        (finitePlaceLowerCharacter (rationalPrimePlace p (Fact.out : p.Prime)) z₁ z₂))
      (finitePlaceInducedSpherical (rationalPrimePlace p (Fact.out : p.Prime)) z₁ z₂) =
    ((p : ℂ) * (z₁⁻¹ : ℂˣ) + (z₂⁻¹ : ℂˣ)) •
      finitePlaceInducedSpherical (rationalPrimePlace p (Fact.out : p.Prime)) z₁ z₂ := by
  have he := finitePlaceInducedSpherical_fixed_line
    (rationalPrimePlace p (Fact.out : p.Prime)) z₁ z₂
    (finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) _
      (finitePlaceInducedSpherical (rationalPrimePlace p (Fact.out : p.Prime)) z₁ z₂))
    (finitePlaceHeckeTrace_level_fixed 1 p (Nat.coprime_one_right p) _ _
      (finitePlaceInducedSpherical_fixed _ z₁ z₂))
  rw [finitePlaceInducedSpherical_hecke_identity] at he
  exact he

end
end Dubon2026
