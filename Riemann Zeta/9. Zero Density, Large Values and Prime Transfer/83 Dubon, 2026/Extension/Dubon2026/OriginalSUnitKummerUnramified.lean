import Dubon2026.OriginalInertiaUnitRadicalFixed
import Dubon2026.OriginalSUnitSelectedKernel

/-! # Outside unramifiedness of the actual full S-unit Kummer field

Every generating radical has radicand equal to an S-unit times a global
power. Divide by the actual base-field root of that power, apply the
proved unit-radical inertia argument, and use generation. This discharges
the upper-prime unramifiedness input to DUB-17's large-support norm field.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n]
local notation "N" => OriginalSUnitKummerField K Ω S n
variable [FiniteDimensional K (OriginalSUnitKummerField K Ω S n)]
  [NumberField (OriginalSUnitKummerField K Ω S n)]
  [IsGalois K (OriginalSUnitKummerField K Ω S n)]

omit [FiniteDimensional K (OriginalSUnitKummerField K Ω S n)]
  [IsGalois K (OriginalSUnitKummerField K Ω S n)] in
/-- The actual full S-unit radical field has trivial inertia outside S
at every prime where its exponent is a unit. -/
theorem originalSUnitKummer_inertia_eq_bot
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 N))
    [w.asIdeal.LiesOver v.asIdeal] (hv : v ∉ S) (hn : (n : 𝓞 K) ∉ v.asIdeal) :
    w.asIdeal.inertia Gal(N/K) = ⊥ := by
  let Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range
  have hnBase : v.valuation K (n : K) = 1 := by
    simpa only [map_natCast] using (v.valuation_eq_one_iff_notMem (K := K)).mpr hn
  have hnUpper : w.valuation N (n : N) = 1 := by
    rw [← map_natCast (algebraMap K N), original_valuation_algebraMap_pow K N v w,
      hnBase, one_pow]
  apply le_antisymm _ bot_le
  intro σ hσ
  change σ = 1
  apply AlgEquiv.coe_algHom_injective
  apply IntermediateField.adjoin_algHom_ext K
  intro β hβ
  let root : originalKummerRootSet (Ω := Ω) n Δ := ⟨β, hβ⟩
  let a : Δ := root.property.choose
  let b : Nˣ := originalKummerRootUnit n Δ root
  have hb : (b : N) ^ n = algebraMap K N (a.val : K) :=
    congrArg Units.val (originalKummerRootUnit_pow n Δ root)
  obtain ⟨u, hu, z, hz, huz⟩ := Subgroup.mem_sup.mp a.property
  obtain ⟨c, rfl⟩ := hz
  have hc : algebraMap K N (c : K) ≠ 0 := (map_ne_zero (algebraMap K N)).mpr c.ne_zero
  let γ : Nˣ := b / Units.map (algebraMap K N).toMonoidHom c
  have hγval : (γ : N) = (b : N) / algebraMap K N (c : K) :=
    Units.val_div_eq_div_val _ _
  have hγ : (γ : N) ^ n = algebraMap K N (u : K) := by
    rw [hγval, div_pow, hb, ← huz]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, powMonoidHom_apply, map_mul, map_pow]
    exact mul_div_cancel_right₀ _ (pow_ne_zero _ hc)
  have hγPower : w.valuation N (γ : N) ^ n = 1 := by
    rw [← map_pow, hγ, original_valuation_algebraMap_pow K N v w, hu v hv, one_pow]
  have hγUnit : w.valuation N (γ : N) = 1 :=
    (pow_eq_one_iff_of_nonneg zero_le (NeZero.ne n)).mp hγPower
  have hfix := originalInertia_fixes_unit_radical K N w n hnUpper u γ hγ hγUnit σ hσ
  rw [hγval, map_div₀, σ.commutes] at hfix
  exact (div_left_inj' hc).mp hfix

/-- The actual full S-unit Kummer field is absolutely unramified above
every unramified base prime outside S where the exponent is a unit. -/
theorem originalSUnitKummer_unramified
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 N))
    [w.asIdeal.LiesOver v.asIdeal] (hv : v ∉ S) (hn : (n : 𝓞 K) ∉ v.asIdeal)
    (hBase : Algebra.IsUnramifiedAt ℤ v.asIdeal) :
    Algebra.IsUnramifiedAt ℤ w.asIdeal := by
  have hInertia := originalSUnitKummer_inertia_eq_bot K Ω S n v w hv hn
  have hIndex : v.asIdeal.ramificationIdx w.asIdeal = 1 := by
    rw [← numberField_card_inertia_eq_ramificationIdx v w, hInertia]
    exact Nat.card_unique
  letI : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    (numberField_isUnramifiedAt_iff_ramificationIdx_one v w).mpr hIndex
  letI : Algebra.IsUnramifiedAt ℤ v.asIdeal := hBase
  exact Algebra.IsUnramifiedAt.comp (R := ℤ) v.asIdeal w.asIdeal

end
end Dubon2026
