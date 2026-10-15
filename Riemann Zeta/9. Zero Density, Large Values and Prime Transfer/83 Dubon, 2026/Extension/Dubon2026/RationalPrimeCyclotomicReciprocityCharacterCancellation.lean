import Dubon2026.RationalPrimeCyclotomicReciprocityRationalUnitCancellation

/-! # Exact character cancellation for the ramified rational-unit action

The previously proved root cancellation already determines an identity in
the unit group of the prime-power residue ring.  This module records that
identity explicitly: the actual ramified reciprocity character multiplied by
the forward quotient unit is one.  The cyclotomic principal-product endpoint
therefore needs only identify the signed away-product unit with this named
forward unit.
-/
namespace Dubon2026
noncomputable section

open IsDedekindDomain HeightOneSpectrum Metric
open scoped ValuativeRel

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

private theorem primitiveRoot_autToPow_mul_forwardUnit_eq_one
    (K L : Type*) [CommRing K] [Field L] [Algebra K L]
    (N : ℕ) [NeZero N] {ζ : L} (hζ : IsPrimitiveRoot ζ N)
    (σ : L ≃ₐ[K] L) (e : ℕ) (he : e.Coprime N)
    (hcancel : (σ ζ) ^ e = ζ) :
    hζ.autToPow K σ * ZMod.unitOfCoprime e he = 1 := by
  have hpow : ζ ^ ((hζ.autToPow K σ : (ZMod N)ˣ).val.val * e) = ζ ^ 1 := by
    calc
      ζ ^ ((hζ.autToPow K σ : (ZMod N)ˣ).val.val * e) =
          (ζ ^ (hζ.autToPow K σ : (ZMod N)ˣ).val.val) ^ e := by
            rw [pow_mul]
      _ = (σ ζ) ^ e := by rw [hζ.autToPow_spec K]
      _ = ζ := hcancel
      _ = ζ ^ 1 := (pow_one ζ).symm
  have hmod : (hζ.autToPow K σ : (ZMod N)ˣ).val.val * e ≡ 1 [MOD N] := by
    have hm := (hζ.isOfFinOrder (NeZero.ne N)).pow_eq_pow_iff_modEq.mp hpow
    simpa only [hζ.eq_orderOf] using hm
  apply Units.ext
  change (hζ.autToPow K σ : ZMod N) * ((e : ℕ) : ZMod N) = 1
  rw [← ZMod.natCast_zmod_val (hζ.autToPow K σ : ZMod N),
    ← Nat.cast_mul, ← Nat.cast_one]
  exact (ZMod.natCast_eq_natCast_iff _ _ N).2 hmod

/-- Every rational unit admits an actual prime-power cyclotomic stage on
which its ramified reciprocity character is the inverse of the explicit
forward quotient unit. -/
theorem rationalPrimeRationalUnit_exists_reciprocity_character_cancellation
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) (q : ℚˣ) :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    ∃ (a c : ℕ), 0 < a ∧ 0 < c ∧ ¬p ∣ c ∧
      ∃ ha : ¬p ∣ a, ∃ u : 𝒪[K]ˣ, ∃ hu : u.val = a, ∃ b d : ℕ,
        ∃ hca : a.Coprime (p ^ (n + 1)),
        ∃ hcd : d.Coprime (p ^ (n + 1)),
        b.Coprime (p ^ (n + 1)) ∧ c.Coprime (p ^ (n + 1)) ∧
        a * b ≡ 1 [MOD p ^ (n + 1)] ∧
        c * d ≡ 1 [MOD p ^ (n + 1)] ∧
        let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
        letI : IsCyclic Gal(L/K) :=
          rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
        let ζ := rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha
        let σ := (localFieldFiniteCyclicReciprocity K Ω L
          (Additive.ofMul (rationalPrimeRationalUnit p hp q))).toMul
        letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
        σ ζ = ζ ^ (b * c) ∧
        (σ ζ) ^ (a * d) = ζ ∧
        (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive p hp n a u hu ha).autToPow
            K σ *
          ZMod.unitOfCoprime (a * d)
            (hca.mul_left hcd) = 1 := by
  dsimp only
  obtain ⟨a, c, ha0, hc0, hc, ha, u, hu, b, d,
      hca, hcb, hcc, hcd, hab, hcdinv, haction, hcancel⟩ :=
    rationalPrimeRationalUnit_exists_reciprocity_root_cancellation p hp hp2 n q
  refine ⟨a, c, ha0, hc0, hc, ha, u, hu, b, d,
    hca, hcd, hcb, hcc, hab, hcdinv, haction, hcancel, ?_⟩
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
  letI : IsCyclic Gal(L/K) :=
    rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  let ζ := rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha
  let σ := (localFieldFiniteCyclicReciprocity K Ω L
    (Additive.ofMul (rationalPrimeRationalUnit p hp q))).toMul
  letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact primitiveRoot_autToPow_mul_forwardUnit_eq_one K L (p ^ (n + 1))
    (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive p hp n a u hu ha)
    σ (a * d) (hca.mul_left hcd) hcancel

end
end Dubon2026
