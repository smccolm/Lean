import Dubon2026.PrincipalUpperDescent
import Dubon2026.PrincipalCyclicLocality
import Dubon2026.FiniteCompressionDecomposition

/-! # Common local invariants descend to genuine upper congruence invariants -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section
attribute [local instance] principalNormal
attribute [local instance] primeFactorBaseNeZero primeFactorLevelNeZero primeFactorLowerFintype

/-- A finite product of commuting endomorphisms fixes every common fixed vector. -/
theorem noncommProd_end_fixed {I V : Type*} [AddCommGroup V] [Module ℂ V]
    (s : Finset I) (e : I → V →ₗ[ℂ] V)
    (he : Set.Pairwise (↑s) (fun i j => Commute (e i) (e j)))
    (x : V) (hx : ∀ i ∈ s, e i x = x) : s.noncommProd e he x = x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi, Module.End.mul_apply,
      ih _ (fun j hj => hx j (Finset.mem_insert_of_mem hj)), hx i (Finset.mem_insert_self i s)]

/-- The literal product of all actual local lower-triangular averaging operators. -/
def principalCommonLowerProjection (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    principalCuspOrbit N k f →ₗ[ℂ] principalCuspOrbit N k f :=
  Finset.univ.noncommProd (principalLowerProjection N k f)
    (fun p _ q _ hpq => principalLowerProjection_commute N k f p q hpq)

/-- Every local lower-triangular average fixes the common projection. -/
theorem principalLowerProjection_mul_common (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (p : N.primeFactors) :
    principalLowerProjection N k f p * principalCommonLowerProjection N k f =
      principalCommonLowerProjection N k f :=
  idempotent_mul_noncommProd _ _ _ (fun q _ => principalLowerProjection_idempotent N k f q)
    p (Finset.mem_univ p)

/-- The product of all actual local lower averages is idempotent. -/
theorem principalCommonLowerProjection_idempotent (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    IsIdempotentElem (principalCommonLowerProjection N k f) :=
  noncommProd_idempotent _ _ _ (fun p _ => principalLowerProjection_idempotent N k f p)

/-- The rescaled actual Gamma0 source lies in the common invariant range. -/
theorem principalCommonLowerProjection_rescaled_fixed (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    principalCommonLowerProjection N k (cuspRescaledPrincipal N k f)
      ⟨cuspRescaledPrincipal N k f, mem_principalCuspOrbit N k _⟩ =
        ⟨cuspRescaledPrincipal N k f, mem_principalCuspOrbit N k _⟩ :=
  noncommProd_end_fixed _ _ _ _ (fun p _ => principalLowerProjection_rescaled_fixed N k f p)

/-- Every element of the principal congruence quotient is the product of its actual local embeddings. -/
theorem principalPrimeFactors_product (N : ℕ) [NeZero N] (g : SL(2, ℤ) ⧸ Gamma N) :
    Finset.univ.noncommProd
      (fun p : N.primeFactors => principalPrimeFactorEmbedding N p (principalPrimeFactorsEquiv N g p))
      (fun p _ q _ hpq => principalPrimeFactorEmbedding_commute N p q hpq _ _) = g := by
  apply (principalPrimeFactorsEquiv N).injective
  rw [Finset.map_noncommProd]
  simp only [principalPrimeFactorEmbedding_components]
  exact Finset.noncommProd_mulSingle _

/-- Common local lower invariance implies the genuine integral upper congruence transformation law. -/
theorem principalCommonLowerProjection_upper (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (v : principalCuspOrbit N k f)
    (hv : v ∈ LinearMap.range (principalCommonLowerProjection N k f)) :
    v.val ∈ principalUpperInvariantSpace N k := by
  have hlocal : ∀ p : N.primeFactors, ∀ g : sl2LowerTriangular (ZMod (p.val ^ N.factorization p.val)),
      principalLowerRepresentation N k f p g v = v := by
    intro p
    apply (finiteGroupProjection_eq_self_iff _ _).mp
    obtain ⟨w, rfl⟩ := hv
    exact LinearMap.congr_fun (principalLowerProjection_mul_common N k f p) w
  intro γ
  have hγ := (principalPrimeFactors_upper_iff N γ.val).mpr γ.property
  have he : principalCuspOrbitRepresentation N k f (QuotientGroup.mk γ.val) v = v := by
    rw [← principalPrimeFactors_product N (QuotientGroup.mk γ.val), Finset.map_noncommProd]
    apply noncommProd_end_fixed
    intro p _
    exact hlocal p ⟨_, hγ p⟩
  exact congrArg Subtype.val he

/-- Linear descent of the genuine common invariant range to actual Gamma0 forms. -/
def principalCommonToGamma0 (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    LinearMap.range (principalCommonLowerProjection N k f) →ₗ[ℂ]
      CuspForm ((Gamma0 N).map (mapGL ℝ)) k :=
  (principalUpperToGamma0 N k).comp
    (((principalCuspOrbit N k f).subtype.comp
      (LinearMap.range (principalCommonLowerProjection N k f)).subtype).codRestrict
        (principalUpperInvariantSpace N k)
        (fun v => principalCommonLowerProjection_upper N k f v.val v.property))

/-- The actual descent from the common invariant range preserves all Fourier coefficients. -/
theorem principalCommonToGamma0_coeff (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k)
    (v : LinearMap.range (principalCommonLowerProjection N k f)) (n : ℕ) :
    cuspCoefficients (principalCommonToGamma0 N k f v) n = principalCuspCoefficients v.val.val n :=
  principalUpperToGamma0_coeff N k _ n

end
end Dubon2026
