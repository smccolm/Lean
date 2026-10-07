import Dubon2026.FiniteLowerTriangular
import Dubon2026.FiniteProjectionCommutation
import Dubon2026.PrincipalOrbitProjection

/-! # Actual local lower-triangular averages on the finite cusp orbit -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section
attribute [local instance] principalNormal

local instance primeFactorBaseNeZero (N : ℕ) (p : N.primeFactors) : NeZero p.val :=
  ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩

local instance primeFactorLevelNeZero (N : ℕ) (p : N.primeFactors) :
    NeZero (p.val ^ N.factorization p.val) :=
  ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.property).ne_zero⟩

/-- The actual lower-triangular subgroup over a finite prime-power ring is finite. -/
local instance primeFactorLowerFintype (N : ℕ) (p : N.primeFactors) :
    Fintype (sl2LowerTriangular (ZMod (p.val ^ N.factorization p.val))) := Fintype.ofFinite _

/-- Restrict the genuine local slash action to its actual lower-triangular subgroup. -/
def principalLowerRepresentation (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (p : N.primeFactors) :
    Representation ℂ (sl2LowerTriangular (ZMod (p.val ^ N.factorization p.val)))
      (principalCuspOrbit N k f) :=
  (principalPrimeFactorOrbitRepresentation N k f p).comp (sl2LowerTriangular _).subtype

/-- The literal finite lower-triangular average at one prime-power factor. -/
def principalLowerProjection (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (p : N.primeFactors) :
    principalCuspOrbit N k f →ₗ[ℂ] principalCuspOrbit N k f :=
  finiteGroupProjection (principalLowerRepresentation N k f p)

/-- Each actual local lower-triangular average is idempotent. -/
theorem principalLowerProjection_idempotent (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (p : N.primeFactors) :
    IsIdempotentElem (principalLowerProjection N k f p) := finiteGroupProjection_idempotent _

/-- Different local lower-triangular averages commute on the actual cusp orbit. -/
theorem principalLowerProjection_commute (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (p q : N.primeFactors) (hpq : p ≠ q) :
    Commute (principalLowerProjection N k f p) (principalLowerProjection N k f q) := by
  apply finiteGroupProjection_commute
  intro g h
  exact principalPrimeFactorOrbit_commute N k f p q hpq g.val h.val

/-- The genuine rescaled source vector is fixed by every actual local lower average. -/
theorem principalLowerProjection_rescaled_fixed (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (p : N.primeFactors) :
    principalLowerProjection N k (cuspRescaledPrincipal N k f) p
      ⟨cuspRescaledPrincipal N k f, mem_principalCuspOrbit N k _⟩ =
        ⟨cuspRescaledPrincipal N k f, mem_principalCuspOrbit N k _⟩ := by
  apply (finiteGroupProjection_eq_self_iff _ _).mpr
  intro g
  apply Subtype.ext
  exact cuspRescaledPrincipal_local_lower_fixed N k f p g

/-- One proved invariant auxiliary inner product makes both families of genuine averages symmetric. -/
theorem principalLowerDivisor_commonCore (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    ∃ c : InnerProductSpace.Core ℂ (principalCuspOrbit N k f),
      (∀ (p : N.primeFactors) (x y : principalCuspOrbit N k f),
        c.inner (principalLowerProjection N k f p x) y =
          c.inner x (principalLowerProjection N k f p y)) ∧
      (∀ (d : ℕ) [NeZero d] (hd : d ∣ N) (x y : principalCuspOrbit N k f),
        c.inner (principalOrbitDivisorProjection hd k f x) y =
          c.inner x (principalOrbitDivisorProjection hd k f y)) := by
  obtain ⟨c, hc⟩ := principalCuspOrbit_invariantCore N k f
  refine ⟨c, ?_, ?_⟩
  · intro p x y
    letI := c
    letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := principalCuspOrbit N k f)
    letI := InnerProductSpace.ofCore c.toCore
    exact (finiteGroupProjection_symmetric (principalLowerRepresentation N k f p)
      (fun g u v => hc (principalPrimeFactorEmbedding N p g.val) u v)).isSymmetric x y
  · intro d _ hd x y
    letI := c
    letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := principalCuspOrbit N k f)
    letI := InnerProductSpace.ofCore c.toCore
    exact (finiteCyclicProjection_symmetric (principalCuspOrbitRepresentation N k f)
      hc d (principalCyclicGenerator N d) (principalCyclicGenerator_pow hd)).isSymmetric x y

end
end Dubon2026
