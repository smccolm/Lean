import Dubon2026.ContinuousKummerH2Maps
import Dubon2026.GaloisRadicalClassIndependence

/-! # The original radicals of actual root-valued continuous one-cocycles

These identify the degree-one Kummer classes needed to connect local cup
nondegeneracy with the proved cyclic norm pairing. No local duality is assumed.
-/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Every actual continuous root-valued one-cocycle is realized by the Galois
ratios of an original extension-field radical of an original base-field unit. -/
theorem continuousRootOneCocycle_exists_radical
    (c : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)) :
    ∃ (a : Kˣ) (β : Ωˣ),
      β ^ n = Units.map (algebraMap K Ω).toMonoidHom a ∧
      ∀ g : Gal(Ω/K), g • β / β =
        ((Additive.toMul (Rep.toAdditive (c.val g)) : rootsOfUnity n Ω) : Ωˣ) := by
  let d := continuousCoefficientCocycleOneMap
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) (Rep.ofAlgebraAutOnUnits K Ω)
    (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap
    (galoisKummerInclusion_continuous (K := K) (Ω := Ω) n)
    (Rep.hom_comm_apply (galoisKummerInclusion (K := K) (Ω := Ω) n)) c
  obtain ⟨β, hβ⟩ := continuousInfiniteGaloisUnitCocycle_exists_unit d
  have hratio : ∀ g : Gal(Ω/K), g • β / β =
      ((Additive.toMul (Rep.toAdditive (c.val g)) : rootsOfUnity n Ω) : Ωˣ) := hβ
  have hfixed : ∀ g : Gal(Ω/K), g ((β : Ω) ^ n) = (β : Ω) ^ n := by
    intro g
    have h := congrArg (fun z : Ωˣ => z ^ n) (hratio g)
    dsimp only at h
    rw [div_pow, (Additive.toMul (Rep.toAdditive (c.val g)) : rootsOfUnity n Ω).property] at h
    have hval := congrArg Units.val (div_eq_one.mp h)
    simpa only [Units.val_pow_eq_pow_val, AlgEquiv.smul_units_def,
      Units.coe_map, MonoidHom.coe_coe, map_pow] using hval
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed ((β : Ω) ^ n)).mpr hfixed
  have ha0 : a ≠ 0 := by
    intro hzero
    exact pow_ne_zero n β.ne_zero (by simpa only [hzero, map_zero] using ha.symm)
  exact ⟨Units.mk0 a ha0, β, Units.ext ha.symm, hratio⟩

/-- The original root-valued H1 class vanishes exactly when its actual radical
power is an nth power in the original base field. This is proved with the actual
root coboundary witness, not an assumed Kummer identification. -/
theorem continuousRootOneCocycle_class_zero_iff_power
    (c : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
    (a : Kˣ) (β : Ωˣ)
    (hβ : β ^ n = Units.map (algebraMap K Ω).toMonoidHom a)
    (hratio : ∀ g : Gal(Ω/K), g • β / β =
      ((Additive.toMul (Rep.toAdditive (c.val g)) : rootsOfUnity n Ω) : Ωˣ)) :
    (Submodule.Quotient.mk c : ContinuousRepresentationH1
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
      (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)) = 0 ↔
        a ∈ (powMonoidHom n : Kˣ →* Kˣ).range := by
  constructor
  · intro hz
    obtain ⟨δ, hδ⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
    let γ : Ωˣ := (Additive.toMul (Rep.toAdditive δ) : rootsOfUnity n Ω).val
    have hγ : γ ^ n = Units.map (algebraMap K Ω).toMonoidHom 1 := by
      rw [map_one]
      exact (Additive.toMul (Rep.toAdditive δ) : rootsOfUnity n Ω).property
    have hratios : ∀ g : Gal(Ω/K), g • β / β = g • γ / γ := by
      intro g
      rw [hratio]
      have h := congrArg (fun z : continuousRepresentationCocyclesOne
        (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) =>
          ((Additive.toMul (Rep.toAdditive (z.val g)) : rootsOfUnity n Ω) : Ωˣ)) hδ
      exact h.symm
    have he := galois_radical_power_class_eq_of_ratios n a 1 β γ hβ hγ hratios
    apply (QuotientGroup.eq_one_iff a).mp
    simpa only [map_one] using he
  · rintro ⟨u, hu⟩
    change u ^ n = a at hu
    let v := Units.map (algebraMap K Ω).toMonoidHom u
    let γ := β / v
    have hγ : γ ^ n = 1 := by
      dsimp only [γ, v]
      rw [div_pow, ← map_pow, hu, hβ, div_self']
    let δ : galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n :=
      Rep.toAdditive.symm (Additive.ofMul (⟨γ, hγ⟩ : rootsOfUnity n Ω))
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨δ, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext g
    apply Rep.toAdditive.injective
    apply Subtype.ext
    change g • γ / γ =
      ((Additive.toMul (Rep.toAdditive (c.val g)) : rootsOfUnity n Ω) : Ωˣ)
    rw [← hratio]
    dsimp only [γ, v]
    rw [smul_div', galois_base_unit_fixed]
    exact div_div_div_cancel_right _ _ _

/-- Two original root H1 classes agree exactly when their actual radical powers
agree modulo nth powers in the original base field. -/
theorem continuousRootOneCocycle_class_eq_iff_power_class
    (c d : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
    (a b : Kˣ) (β γ : Ωˣ)
    (hβ : β ^ n = Units.map (algebraMap K Ω).toMonoidHom a)
    (hγ : γ ^ n = Units.map (algebraMap K Ω).toMonoidHom b)
    (hc : ∀ g : Gal(Ω/K), g • β / β =
      ((Additive.toMul (Rep.toAdditive (c.val g)) : rootsOfUnity n Ω) : Ωˣ))
    (hd : ∀ g : Gal(Ω/K), g • γ / γ =
      ((Additive.toMul (Rep.toAdditive (d.val g)) : rootsOfUnity n Ω) : Ωˣ)) :
    (Submodule.Quotient.mk c : ContinuousRepresentationH1
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
      (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)) =
        Submodule.Quotient.mk d ↔
      QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range a =
        QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range b := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub]
  apply Iff.trans (b := a / b ∈ (powMonoidHom n : Kˣ →* Kˣ).range) ?_
    QuotientGroup.eq_iff_div_mem.symm
  apply continuousRootOneCocycle_class_zero_iff_power n (c - d) (a / b) (β / γ)
  · rw [div_pow, hβ, hγ, map_div]
  · intro g
    change g • (β / γ) / (β / γ) =
      ((Additive.toMul (Rep.toAdditive (c.val g)) : rootsOfUnity n Ω) : Ωˣ) /
        ((Additive.toMul (Rep.toAdditive (d.val g)) : rootsOfUnity n Ω) : Ωˣ)
    rw [smul_div', div_div_div_comm, hc, hd]

end
end Dubon2026
