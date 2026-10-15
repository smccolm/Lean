import Dubon2026.RationalPrimeOriginalCyclotomicClosureStageIndependence
import Dubon2026.RationalPrimeChangedCyclotomicClosureNaturalUnitAction

/-! # Quotient actions on the actual cyclotomic closure stage

The natural-unit reciprocity formula is multiplicative, but numerator and
denominator are constructed through separately chosen algebraic-closure
embeddings.  This module supplies the exact algebra needed to combine them.

First, an action formula on a primitive root determines the inverse action.
Second, an additive homomorphism from multiplicative units sends a quotient
to the expected quotient automorphism.  Third, cyclicity transports an action
formula back across a conjugating stage automorphism.  Equality of finite
Galois stages also transports the finite cyclic reciprocity map itself.

The final theorem applies these facts to two positive natural units in one
fixed actual cyclotomic closure stage.  It is the algebraic numerator and
denominator assembly required before constructing the arbitrary rational-unit
wrapper in DUB-17.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

set_option maxHeartbeats 1200000

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

/-- If an automorphism acts by `d` on a primitive `m`-th root and `c` is the
inverse of `d` modulo `m`, its inverse automorphism acts by `c`. -/
theorem algEquiv_inv_primitiveRoot_action
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (m c d : ℕ) (hm : m ≠ 0) (ζ : L) (hζ : IsPrimitiveRoot ζ m)
    (g : L ≃ₐ[K] L) (hg : g ζ = ζ ^ d)
    (hdc : d * c ≡ 1 [MOD m]) :
    g⁻¹ ζ = ζ ^ c := by
  apply g.injective
  change g (g.symm ζ) = g (ζ ^ c)
  rw [g.apply_symm_apply, map_pow, hg, ← pow_mul]
  calc
    ζ = ζ ^ 1 := (pow_one ζ).symm
    _ = ζ ^ (d * c) :=
      (hζ.isOfFinOrder hm).pow_eq_pow_iff_modEq.mpr (by
        simpa only [hζ.eq_orderOf] using hdc.symm)

/-- Numerator and denominator actions on one primitive root combine through
an additive homomorphism on multiplicative units. -/
theorem addMonoidHom_quotient_primitiveRoot_action
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (ρ : Additive Kˣ →+ Additive Gal(L/K))
    (m b c d : ℕ) (hm : m ≠ 0) (ζ : L) (hζ : IsPrimitiveRoot ζ m)
    (u v : Kˣ)
    (hu : (ρ (Additive.ofMul u)).toMul ζ = ζ ^ b)
    (hv : (ρ (Additive.ofMul v)).toMul ζ = ζ ^ d)
    (hdc : d * c ≡ 1 [MOD m]) :
    (ρ (Additive.ofMul (u / v))).toMul ζ = ζ ^ (b * c) := by
  let gu := (ρ (Additive.ofMul u)).toMul
  let gv := (ρ (Additive.ofMul v)).toMul
  have hvinv : gv⁻¹ ζ = ζ ^ c :=
    algEquiv_inv_primitiveRoot_action m c d hm ζ hζ gv hv hdc
  change (ρ (Additive.ofMul u - Additive.ofMul v)).toMul ζ = _
  rw [map_sub]
  change (gu * gv⁻¹) ζ = _
  change gu (gv⁻¹ ζ) = _
  rw [hvinv, map_pow, hu, ← pow_mul]

attribute [local instance] IsCyclic.commGroup

/-- In a cyclic Galois group, an action formula on a conjugate root transports
back to the original root. -/
theorem cyclic_action_of_conjugate_root_action
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L : FiniteGaloisIntermediateField K Ω) [IsCyclic Gal(L/K)]
    (g τ : Gal(L/K)) (x y : L) (d : ℕ)
    (hxy : τ x = y) (hy : g y = y ^ d) :
    g x = x ^ d := by
  have hcomm : g * τ = τ * g := mul_comm g τ
  apply τ.injective
  calc
    τ (g x) = g (τ x) := DFunLike.congr_fun hcomm.symm x
    _ = g y := by rw [hxy]
    _ = y ^ d := hy
    _ = (τ x) ^ d := by rw [hxy]
    _ = τ (x ^ d) := by rw [map_pow]

/-- Equality of finite Galois intermediate fields induces the literal
equivalence of their automorphism groups. -/
def finiteGaloisStageAutCast
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {L M : FiniteGaloisIntermediateField K Ω} (h : L = M) :
    Gal(L/K) ≃* Gal(M/K) := by
  subst M
  exact MulEquiv.refl _

/-- Casting an element along equality of finite intermediate stages preserves
its value in the common ambient field. -/
@[simp] theorem finiteGaloisStage_cast_coe
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {L M : FiniteGaloisIntermediateField K Ω} (h : L = M) (x : L) :
    (((h ▸ x : M) : Ω)) = (x : Ω) := by
  subst M
  rfl

/-- The automorphism-group cast acts on the corresponding cast field value. -/
@[simp] theorem finiteGaloisStageAutCast_apply
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {L M : FiniteGaloisIntermediateField K Ω} (h : L = M)
    (g : Gal(L/K)) (x : L) :
    finiteGaloisStageAutCast h g (h ▸ x) = h ▸ g x := by
  subst M
  rfl

/-- Finite cyclic reciprocity is unchanged when its finite intermediate stage
is rewritten along an equality. -/
theorem localFieldFiniteCyclicReciprocity_stage_cast
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    [IsSepClosed Ω] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    {L M : FiniteGaloisIntermediateField K Ω}
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (h : L = M) (u : Kˣ) :
    finiteGaloisStageAutCast h
        (localFieldFiniteCyclicReciprocity K Ω L (Additive.ofMul u)).toMul =
      (localFieldFiniteCyclicReciprocity K Ω M (Additive.ofMul u)).toMul := by
  subst M
  rfl

/-- An action formula for finite cyclic reciprocity transports from an equal
stage and a conjugate root back to the chosen stage and root. -/
theorem localFieldFiniteCyclicReciprocity_action_transport_stage_eq
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    [IsSepClosed Ω] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
    {L M : FiniteGaloisIntermediateField K Ω}
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (h : L = M) (u : Kˣ) (x : L) (y : M) (τ : Gal(L/K)) (d : ℕ)
    (hxy : τ x = h.symm ▸ y)
    (hy : (localFieldFiniteCyclicReciprocity K Ω M
      (Additive.ofMul u)).toMul y = y ^ d) :
    (localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul u)).toMul x = x ^ d := by
  subst M
  exact cyclic_action_of_conjugate_root_action L
    (localFieldFiniteCyclicReciprocity K Ω L (Additive.ofMul u)).toMul
    τ x y d hxy hy

/-- The actual closure-stage root retains its exact prime-power order. -/
theorem rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    IsPrimitiveRoot
      (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha)
      (p ^ (n + 1)) := by
  let e := rationalPrimeOriginalCyclotomicClosureEquiv p hp n a u hu ha
  have h := (rationalPrimeOriginalCyclotomicStageRoot_isPrimitive p hp n).map_of_injective
    e.injective
  exact h

/-- The literal quotient of two positive natural units in the rational local
field. -/
def rationalPrimeNaturalQuotientUnit
    (p : ℕ) (hp : p.Prime) (a c : ℕ) (ha : ¬p ∣ a) (hc : ¬p ∣ c) :
    (rationalPrimeLocalField p hp)ˣ :=
  rationalPrimeNaturalUnit p hp a ha / rationalPrimeNaturalUnit p hp c hc

/-- The natural quotient unit has literal field value `a / c`. -/
@[simp] theorem rationalPrimeNaturalQuotientUnit_val
    (p : ℕ) (hp : p.Prime) (a c : ℕ) (ha : ¬p ∣ a) (hc : ¬p ∣ c) :
    (rationalPrimeNaturalQuotientUnit p hp a c ha hc :
      rationalPrimeLocalField p hp) = a / c := rfl

/-- On one fixed actual cyclotomic closure stage, the numerator inverse
exponent and denominator inverse exponent combine to the inverse exponent of
their quotient. -/
theorem rationalPrimeNaturalQuotient_reciprocity_root
    (p : ℕ) (hp : p.Prime) (n a b c d : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    [IsCyclic Gal(rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha /
      rationalPrimeLocalField p hp)]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
    (hc : ¬p ∣ c)
    (hA :
      (localFieldFiniteCyclicReciprocity (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)
        (rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha)
        (Additive.ofMul (rationalPrimeNaturalUnit p hp a ha))).toMul
          (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) =
        (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ b)
    (hC :
      (localFieldFiniteCyclicReciprocity (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp)
        (rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha)
        (Additive.ofMul (rationalPrimeNaturalUnit p hp c hc))).toMul
          (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) =
        (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ d)
    (hdc : d * c ≡ 1 [MOD p ^ (n + 1)]) :
    (localFieldFiniteCyclicReciprocity (rationalPrimeLocalField p hp)
      (rationalPrimeLocalClosure p hp)
      (rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha)
      (Additive.ofMul
        (rationalPrimeNaturalQuotientUnit p hp a c ha hc))).toMul
        (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) =
      (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ (b * c) := by
  exact addMonoidHom_quotient_primitiveRoot_action
    (localFieldFiniteCyclicReciprocity (rationalPrimeLocalField p hp)
      (rationalPrimeLocalClosure p hp)
      (rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha))
    (p ^ (n + 1)) b c d (pow_ne_zero _ hp.ne_zero)
    (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha)
    (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive p hp n a u hu ha)
    (rationalPrimeNaturalUnit p hp a ha) (rationalPrimeNaturalUnit p hp c hc)
    hA hC hdc

/-- The witness-producing natural-unit theorem has a compact action-only
consequence: all auxiliary local-field and uniformizer witnesses are consumed
internally, while the actual root action and modular inverse remain. -/
theorem rationalPrimeNaturalUnit_exists_reciprocity_root_action
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n a : ℕ) (ha : ¬p ∣ a) :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    ∃ u : 𝒪[K]ˣ, ∃ hu : u.val = a, ∃ b : ℕ,
      a.Coprime (p ^ (n + 1)) ∧ b.Coprime (p ^ (n + 1)) ∧
      a * b ≡ 1 [MOD p ^ (n + 1)] ∧
      let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
      letI : IsCyclic Gal(L/K) :=
        rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
      (localFieldFiniteCyclicReciprocity K Ω L
        (Additive.ofMul (rationalPrimeNaturalUnit p hp a ha))).toMul
          (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) =
        (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ b := by
  dsimp only
  have h := rationalPrimeNaturalUnitChangedCyclotomicClosure_reciprocity_root
    p hp hp2 n a ha
  dsimp only at h
  simp only [rationalPrimePlace_natGenerator] at h
  obtain ⟨u, hu, b, hca, hcb, hab, hrest⟩ := h
  obtain ⟨fdE, valE, topE, localE, extKE, valM, topM, localM, extKM, extEM, hdata⟩ :=
    hrest
  let K := rationalPrimeLocalField p hp
  let E := rationalPrimeChangedAuxiliaryClosureField p hp n a u hu ha
  let M := rationalPrimeChangedCyclotomicClosureCompositum p hp n a u hu ha
  letI : FiniteDimensional K E := fdE
  letI : ValuativeRel E := valE
  letI : TopologicalSpace E := topE
  letI : IsNonarchimedeanLocalField E := localE
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) := extKE
  letI : ValuativeRel M := valM
  letI : TopologicalSpace M := topM
  letI : IsNonarchimedeanLocalField M := localM
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M) := extKM
  letI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M) := extEM
  obtain ⟨_θE, _hθE, _hunramified, _hnorm, haction⟩ := hdata
  exact ⟨u, hu, b, hca, hcb, hab, haction⟩

/-- Every quotient `a / c` of positive natural units away from an odd prime
constructs its numerator and denominator actions, rewrites the two separately
chosen cyclotomic stages into one actual field, and acts on the chosen root by
the literal inverse quotient exponent `b * c`. -/
theorem rationalPrimeNaturalQuotient_exists_reciprocity_root_action
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n a c : ℕ)
    (ha : ¬p ∣ a) (hc : ¬p ∣ c) :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    ∃ u : 𝒪[K]ˣ, ∃ hu : u.val = a, ∃ b d : ℕ,
      a.Coprime (p ^ (n + 1)) ∧ b.Coprime (p ^ (n + 1)) ∧
      c.Coprime (p ^ (n + 1)) ∧ d.Coprime (p ^ (n + 1)) ∧
      a * b ≡ 1 [MOD p ^ (n + 1)] ∧
      c * d ≡ 1 [MOD p ^ (n + 1)] ∧
      let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
      letI : IsCyclic Gal(L/K) :=
        rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
      (localFieldFiniteCyclicReciprocity K Ω L
        (Additive.ofMul (rationalPrimeNaturalQuotientUnit p hp a c ha hc))).toMul
          (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) =
        (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ (b * c) := by
  dsimp only
  obtain ⟨u, hu, b, hca, hcb, hab, hA⟩ :=
    rationalPrimeNaturalUnit_exists_reciprocity_root_action p hp hp2 n a ha
  obtain ⟨v, hv, d, hcc, hcd, hcdinv, hC⟩ :=
    rationalPrimeNaturalUnit_exists_reciprocity_root_action p hp hp2 n c hc
  refine ⟨u, hu, b, d, hca, hcb, hcc, hcd, hab, hcdinv, ?_⟩
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let La := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
  let Lc := rationalPrimeOriginalCyclotomicClosureStage p hp n c v hv hc
  letI : IsCyclic Gal(La/K) :=
    rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
  letI : IsCyclic Gal(Lc/K) :=
    rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n c v hv hc
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  let ζa := rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha
  let ζc := rationalPrimeOriginalCyclotomicClosureRoot p hp n c v hv hc
  have hA' :
      (localFieldFiniteCyclicReciprocity K Ω La
        (Additive.ofMul (rationalPrimeNaturalUnit p hp a ha))).toMul ζa = ζa ^ b := by
    exact hA
  have hC' :
      (localFieldFiniteCyclicReciprocity K Ω Lc
        (Additive.ofMul (rationalPrimeNaturalUnit p hp c hc))).toMul ζc = ζc ^ d := by
    exact hC
  have hL : La = Lc :=
    rationalPrimeOriginalCyclotomicClosureStage_eq p hp n a c u hu ha v hv hc
  let τ : Gal(La/K) :=
    rationalPrimeOriginalCyclotomicClosureStageAut p hp n a c u hu ha v hv hc
  have hrootΩ := rationalPrimeOriginalCyclotomicClosureStageAut_root
    p hp n a c u hu ha v hv hc
  have hroot : τ ζa = hL.symm ▸ ζc := by
    apply Subtype.ext
    exact hrootΩ.trans (finiteGaloisStage_cast_coe hL.symm ζc).symm
  have hCcommon :
      (localFieldFiniteCyclicReciprocity K Ω La
        (Additive.ofMul (rationalPrimeNaturalUnit p hp c hc))).toMul ζa = ζa ^ d :=
    localFieldFiniteCyclicReciprocity_action_transport_stage_eq
      hL (rationalPrimeNaturalUnit p hp c hc) ζa ζc τ d hroot hC'
  exact rationalPrimeNaturalQuotient_reciprocity_root
    p hp n a b c d u hu ha hc hA' hCcommon (by
      simpa only [Nat.mul_comm] using hcdinv)

end
end Dubon2026
