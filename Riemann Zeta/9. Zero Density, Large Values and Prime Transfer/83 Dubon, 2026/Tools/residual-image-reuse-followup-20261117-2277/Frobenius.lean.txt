import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Cardinality
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.NumberTheory.RamificationInertia

namespace LocalRing

variable {A B: Type _} [CommRing B] [CommRing A] [LocalRing A] [LocalRing B]
  [Algebra A B] [IsLocalRingHom (algebraMap A B)]

/-- A local ring automorphism is local. -/
instance (e : B ≃+* B) :
    IsLocalRingHom e.toRingHom where
  map_nonunit := by
    rintro b ⟨u, hu⟩
    use Units.map e.symm.toRingHom.toMonoidHom u
    change e.symm u = b
    change (u : B) = e b at hu
    rw [hu]
    simp only [RingEquiv.symm_apply_apply]

noncomputable instance generalAlgebraMap :
    Algebra (LocalRing.ResidueField A) (LocalRing.ResidueField B) :=
  RingHom.toAlgebra (LocalRing.ResidueField.map (algebraMap A B))

/-- The group homomorphism from the Galois group to the Galois group of residue fields. -/
noncomputable def algebraEquivToResidueEquiv :
    (B ≃ₐ[A] B) →* LocalRing.ResidueField B ≃ₐ[LocalRing.ResidueField A] LocalRing.ResidueField B
    where
  toFun x :=
    { toFun := LocalRing.ResidueField.map x.toRingEquiv.toRingHom
      invFun := LocalRing.ResidueField.map x.symm.toRingEquiv.toRingHom
      left_inv := fun y => by simp
      right_inv := fun y => by simp
      map_mul' := fun x y => by simp only [map_mul]
      map_add' := fun x y => by simp only [map_add]
      commutes' := by
        suffices :
          (LocalRing.ResidueField.map x.toRingEquiv.toRingHom).comp
              (algebraMap (ResidueField A) (ResidueField B)) =
            algebraMap (ResidueField A) (ResidueField B)
        rwa [FunLike.ext_iff] at this
        have hres : Function.Surjective (residue A) := by
          exact (Ideal.Quotient.mk (maximalIdeal A)).surjective
        rw [← RingHom.cancel_right hres]
        rw [RingHom.comp_assoc]
        change _ = (LocalRing.ResidueField.map _).comp _
        rw [ResidueField.map_comp_residue]
        change
          (ResidueField.map x.toRingEquiv.toRingHom).comp ((ResidueField.map _).comp _) = _
        rw [ResidueField.map_comp_residue]
        rw [← RingHom.comp_assoc]
        rw [ResidueField.map_comp_residue]
        ext r
        simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_comp, Function.comp_apply]
        simp
       }
  map_one' := by
    ext a
    have hid := ResidueField.map_id_apply a
    apply hid
  map_mul' x y := by
    ext
    simp
    rfl

end LocalRing

namespace ValuationSubring

variable {K L : Type _} [Field K] [Field L]

/-- The map from the pullback of a valuation subring A to A along a ring homomorphism K →+* L -/
def RingHom.valuationSubringComap (A : ValuationSubring L) (f : K →+* L) : comap A f →+* A
    where
  toFun x := ⟨f x.1, x.2⟩
  map_one' := Subtype.eq f.map_one
  map_mul' x y := Subtype.eq (f.map_mul x y)
  map_add' x y := Subtype.eq (f.map_add x y)
  map_zero' := Subtype.eq f.map_zero

/-- The map from the pullback of a valuation subring A to A along a ring homomorphism K →+* L, is local -/
instance valuationSubringComap_local (A : ValuationSubring L) (f : K →+* L) :
    IsLocalRingHom (RingHom.valuationSubringComap A f) where
  map_nonunit := by
    rintro ⟨a, ha⟩ ⟨y, hy : (y : ↥A) = ⟨f a, _⟩⟩
    have hainv : a * a⁻¹ = 1 := by
      apply mul_inv_cancel
      rintro rfl
      have hy0 : (y : A) = 0; simp [hy, f.map_zero]; rfl
      have : (0 : A) ≠ 1 := zero_ne_one
      rw [← zero_mem_nonunits, ← hy0] at this
      exact this (Units.isUnit y)
    refine'
      isUnit_of_mul_eq_one ⟨a, ha⟩ ⟨a⁻¹, (_ : f a⁻¹ ∈ A)⟩ (_ : (⟨a * a⁻¹, _⟩ : A.comap f) = ⟨1, _⟩)
    swap; simp [hainv]
    rcases y with ⟨⟨y1, h₁⟩, ⟨y2, h₂⟩, h1, h2⟩
    convert h₂
    have hy' : y1 = f a; simpa using hy
    have h1' : y1 * y2 = 1 := Subtype.mk.inj h1
    apply_fun f at hainv
    rw [map_mul, map_one] at hainv
    rw [hy'] at h1'
    exact inv_unique hainv h1'

noncomputable instance algebraComap (A : ValuationSubring L) (f : K →+* L) :
    Algebra (LocalRing.ResidueField (comap A f)) (LocalRing.ResidueField A) :=
  RingHom.toAlgebra (LocalRing.ResidueField.map (RingHom.valuationSubringComap A f))

section
--
variable (K) [Field K] [Algebra K L]

open scoped Pointwise

/-- The group homomorphism from the decomposition group to the group
 of automorphisms of the residue field of a valuation subring A-/
def decompositionSubgroupToResidueAut (A : ValuationSubring L) :
    A.decompositionSubgroup K →* RingAut (LocalRing.ResidueField A) :=
  LocalRing.ResidueField.mapAut.comp (MulSemiringAction.toRingAut (A.decompositionSubgroup K) A)

instance AlgebraComap(A : ValuationSubring L) : Algebra (comap A (algebraMap K L)) A :=
  RingHom.toAlgebra (RingHom.valuationSubringComap A (algebraMap K L))

/-- The group homomorphism from the decomposition group to the Galois group of
A fixing the pullback of A. -/
def decompositionSubgroup.restrict (A : ValuationSubring L) :
    A.decompositionSubgroup K →* A ≃ₐ[comap A (algebraMap K L)] A
    where
  toFun x :=
    { MulSemiringAction.toRingAut (A.decompositionSubgroup K) A x with
      commutes' := by
        rintro ⟨r, hr⟩
        cases' x with d hd
        have := d.commutes
        specialize this r
        apply Subtype.ext
        exact this }
  map_one' := by
    ext
    simp only [map_one, AlgEquiv.coe_mk, AlgEquiv.one_apply]
    rfl
  map_mul' := by
    rintro x y
    ext
    simp only [AlgEquiv.mul_apply, AlgEquiv.coe_mk, map_mul]
    rfl

theorem ComapNeTopOfAlgebraic (v : ValuationSubring L) (h : v ≠ ⊤)
    (ha : Algebra.IsAlgebraic K L) : v.comap (algebraMap K L) ≠ ⊤ := sorry

end

namespace frobenius

variable [Fintype K] [Algebra K L]

theorem power {p : ℕ} {m : ℕ} (hp : Nat.Prime p) (hpm : Nat.Prime (p ^ m)) : p = p ^ m :=
  by
  cases' le_or_lt 2 m with hm h
  · exfalso
    exact Nat.Prime.pow_not_prime hm hpm
  · interval_cases m
    rw [pow_zero] at hpm
    exfalso
    have := Nat.Prime.ne_one hpm
    unfold Ne at this
    dsimp only [Not] at this
    apply this
    rfl
    simp only [pow_one]

theorem charP_of_card {p : ℕ} {n : ℕ} (hp : p.Prime) (h : Fintype.card K = p ^ n) : CharP K p :=
  by
  have hyp : addOrderOf (1 : K) ∣ p ^ n := by
    rw [← h]
    apply addOrderOf_dvd_card_univ
  rw [Nat.dvd_prime_pow hp] at hyp
  rcases hyp with ⟨m, hm, hpm⟩
  have hK := CharP.addOrderOf_one K
  rw [hpm] at hK
  have := CharP.char_is_prime K (p ^ m)
  convert hK
  apply power hp this

theorem pow_card_eq {K : Type _} [Field K] [Fintype K] (x : K) : x ^ Fintype.card K = x := by
  rw [FiniteField.pow_card]

variable (K) (L)

def frob : L →ₐ[K] L where
  toFun x := x ^ Fintype.card K
  map_one' := one_pow (Fintype.card K)
  map_mul' x y := mul_pow x y (Fintype.card K)
  map_zero' := by
    simp only [zero_pow_eq_zero]
    exact Fintype.card_pos
  map_add' x y :=
    by
    have foo : IsPrimePow (Fintype.card K) := Fintype.isPrimePow_card_of_field
    unfold IsPrimePow at foo
    rcases foo with ⟨p, k, hp, hk, h⟩
    rw [← h]
    have : Fact (Nat.Prime p) := by
      rw [fact_iff]
      exact Nat.prime_iff.mpr hp
    have : CharP L p := by
      have : CharP K p ↔ CharP L p := Algebra.charP_iff K L p
      rw [← this]
      apply charP_of_card (Nat.prime_iff.mpr hp) h.symm
    apply add_pow_char_pow
  commutes' x :=
    by
    have foo : IsPrimePow (Fintype.card K) := Fintype.isPrimePow_card_of_field
    unfold IsPrimePow at foo
    rcases foo with ⟨p, k, hp, hk, h⟩
    simp
    rw [← h]
    have : Fact (Nat.Prime p) := by
      rw [fact_iff]
      exact Nat.prime_iff.mpr hp
    have : x ^ p ^ k = x := by
      rw [h]
      rw [FiniteField.pow_card]
    rw [← map_pow]
    rw [this]

variable {K} {L}

theorem frob_bijective (ha : Algebra.IsAlgebraic K L) : Function.Bijective (frob K L) :=
  Algebra.IsAlgebraic.algHom_bijective ha _

noncomputable def equiv (ha : Algebra.IsAlgebraic K L) : L ≃ₐ[K] L :=
  AlgEquiv.ofBijective (frob K L) (frob_bijective ha)

end frobenius

open scoped NumberField

variable [NumberField K] [Algebra K L] [IsGalois K L] (K)

instance : IsLocalRingHom (algebraMap { x // x ∈ comap A (algebraMap K L) } { x // x ∈ A }) := sorry

/-- The natural reduction homomorphism from the decomposition group
  to the Galois group of the residue field of A
  fixing the residue field of the pullback of A -/
noncomputable def decompositionSubgroup.toResidueFieldEquiv (A : ValuationSubring L) :
    decompositionSubgroup K A →*
      LocalRing.ResidueField A ≃ₐ[LocalRing.ResidueField (comap A (algebraMap K L))]
        LocalRing.ResidueField A :=
        LocalRing.algebraEquivToResidueEquiv.comp (decompositionSubgroup.restrict K A)

/-- The natural reduction homomorphism is surjective. -/
theorem decompositionSubgroup.surjective (v : ValuationSubring L) :
    Function.Surjective (decompositionSubgroup.toResidueFieldEquiv K v) := sorry

theorem equal_kernels₁ (v : ValuationSubring L) :
    (decompositionSubgroup.toResidueFieldEquiv K v).ker = inertiaSubgroup K v :=
  by
  ext d
  cases' d with d hd
  unfold inertiaSubgroup
  rw [MonoidHom.mem_ker]
  rw [MonoidHom.mem_ker]
  rw [RingEquiv.ext_iff]
  rw [AlgEquiv.ext_iff]
  rfl

/-- If the inertia subgroup is trivial, the natural reduction homomorphism is bijective. -/
theorem decompositionSubgroup.bijective (v : ValuationSubring L) (h : inertiaSubgroup K v = ⊥) :
    Function.Bijective (decompositionSubgroup.toResidueFieldEquiv K v) :=
  by
  constructor
  · have : (decompositionSubgroup.toResidueFieldEquiv K v).ker = ⊥ :=
      by
      rw [equal_kernels₁ K v]
      exact h
    exact (decompositionSubgroup.toResidueFieldEquiv K v).ker_eq_bot_iff.mp this
  · exact decompositionSubgroup.surjective K v

theorem isAlgebraicField : Algebra.IsAlgebraic K L :=
  Normal.isAlgebraic'

theorem algebraComapAlgebraic (B : ValuationSubring L) :
    Algebra.IsAlgebraic (LocalRing.ResidueField (B.comap (algebraMap K L)))
      (LocalRing.ResidueField B) :=
  by
  unfold Algebra.IsAlgebraic
  rintro x
  unfold IsAlgebraic
  have h : Algebra.IsAlgebraic K L := isAlgebraicField K
  unfold Algebra.IsAlgebraic at h
  sorry

variable [NumberField L]

theorem subset_of_val_subring (B : ValuationSubring L) : (𝓞 L).toSubring ≤ B.toSubring :=
  by
  rintro x hx
  simp only [mem_toSubring] at *
  have : x ∈ 𝓞 L := by exact hx
  rw [NumberField.mem_ringOfIntegers L x] at this
  have hB : IsIntegrallyClosed B := by exact IsBezout.instIsIntegrallyClosed
  rw [isIntegrallyClosed_iff L] at hB
  · specialize hB (isIntegral_tower_top_of_isIntegral this : IsIntegral B x)
    rcases hB with ⟨⟨y, hy⟩, rfl⟩
    exact hy

/-- The map (𝓞 L) →+* local_ring.residue_field B -/
def RingOfIntToRes (B : ValuationSubring L) : 𝓞 L →+* LocalRing.ResidueField B :=
  (LocalRing.residue B).comp (Subring.inclusion (subset_of_val_subring B))

/-- The map (𝓞 L) →+* local_ring.residue_field B is surjective-/
theorem RingOfIntToResSurj (B : ValuationSubring L) (htop : B ≠ ⊤) :
    Function.Surjective (RingOfIntToRes B) :=
  by-- have : (ideal.comap (ring_of_int_to_res) (local_ring.maximal_ideal B)).is_prime,
  --{sorry},
  sorry

/-- The isomorphism  (𝓞 L) ⧸ (ring_of_int_to_res B).ker
   ≃+* local_ring.residue_field B -/
noncomputable def resFieldEquiv (B : ValuationSubring L) (htop : B ≠ ⊤) :
    𝓞 L ⧸ RingHom.ker (RingOfIntToRes B) ≃+* LocalRing.ResidueField B :=
  RingHom.quotientKerEquivOfSurjective (RingOfIntToResSurj B htop)

section

theorem FinRakPos : 0 < FiniteDimensional.finrank ℤ (𝓞 L) :=
  by
  rw [NumberField.RingOfIntegers.rank L]
  exact FiniteDimensional.finrank_pos

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The residue field of a number field is finite. -/
theorem ResFieldIsFinite (B : ValuationSubring L) (htop : B ≠ ⊤) :
    Finite (𝓞 L ⧸ RingHom.ker (RingOfIntToRes B)) :=
  by
  have hprime : (RingOfIntToRes B).ker.IsPrime := RingHom.ker_isPrime (RingOfIntToRes B)
  have : Module.Finite ℤ (𝓞 L) := Module.IsNoetherian.finite ℤ (𝓞 L)
  sorry
end

/-- The residue field of a number field is finite. -/
theorem ResFieldFinite (B : ValuationSubring L) (htop : B ≠ ⊤) :
    Finite (LocalRing.ResidueField B) :=
  by
  rw [← (resFieldEquiv B htop).finite_iff]
  exact ResFieldIsFinite B htop

noncomputable def fintypeOfNeBot (B : ValuationSubring K) (htop : B ≠ ⊤) :
    Fintype (LocalRing.ResidueField B) :=
  letI := ResFieldFinite B htop
  Fintype.ofFinite _

/-- The Frobenius element as an element of the decomposition group defined
 as a random pre-image. -/
noncomputable def Frob (K L : Type _) [Field K] [Field L] [NumberField K] [Algebra K L]
    [IsGalois K L] (v : ValuationSubring L) (hv : v ≠ ⊤) : decompositionSubgroup K v :=
  by
  letI :=
    fintypeOfNeBot K (v.comap (algebraMap K L))
      (ComapNeTopOfAlgebraic K v hv Normal.isAlgebraic')
  have := decompositionSubgroup.surjective K v
  let f :
    LocalRing.ResidueField v ≃ₐ[LocalRing.ResidueField (v.comap (algebraMap K L))]
      LocalRing.ResidueField v := frobenius.equiv (algebraComapAlgebraic K v)
  specialize this f
  exact this.choose

section FrobNumberFields

variable [NumberField L]

open IsDedekindDomain

/-- Obtaining the valuation subring of `L` from the nonzero prime
 ideals of its ring of integers-/
noncomputable def _root_.IsDedekindDomain.HeightOneSpectrum.ValuationSubring
  (q : HeightOneSpectrum (𝓞 L)) : ValuationSubring L :=
    q.valuation.valuationSubring

/--The Frobenius element for number fields. -/
noncomputable def frob
  (q : HeightOneSpectrum (𝓞 L)) (htop : q.ValuationSubring ≠ ⊤)
  (h : inertiaSubgroup K q.ValuationSubring = ⊥) :
  (decompositionSubgroup K q.ValuationSubring) :=
  by
    letI :=
      fintypeOfNeBot K (q.ValuationSubring.comap (algebraMap K L))
      (ComapNeTopOfAlgebraic K q.ValuationSubring htop Normal.isAlgebraic')
    exact (Equiv.ofBijective (decompositionSubgroup.toResidueFieldEquiv K q.ValuationSubring)
    (decompositionSubgroup.bijective K q.ValuationSubring h)).symm
     (frobenius.equiv (algebraComapAlgebraic K q.ValuationSubring) )
end FrobNumberFields

end ValuationSubring