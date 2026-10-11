import Dubon2026.HopfBaseChangePoints
import Dubon2026.HopfGaloisStablePointClosure
import Dubon2026.FiniteFreeHopfPoints
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Actual integral point closure through the genuine generic fiber -/

namespace Dubon2026
noncomputable section
open WithConv
open scoped TensorProduct nonZeroDivisors

variable {R F A K : Type*} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F] [CommRing A] [HopfAlgebra R A]
  [Module.Finite R A] [Field K] [Algebra R K] [Algebra F K]
  [IsScalarTower R F K] [Normal F K]

omit [IsDomain R] in
/-- A genuine finite-coordinate point set stable under the original generic-fiber Galois action equals all integral points annihilating its original vanishing ideal. The generic-fiber point theorem and actual denominator clearing derive this equality. -/
theorem localizedHopfPointSet_eq_vanishing
    (X : Set (WithConv (A →ₐ[R] K)))
    (hX : ∀ (g : K ≃ₐ[F] K) (p : WithConv (A →ₐ[R] K)), p ∈ X →
      commutativeHopfPointsAutomorphism (g.restrictScalars R) p ∈ X) :
    X = {p : WithConv (A →ₐ[R] K) |
      hopfPointsVanishingIdeal X ≤ RingHom.ker p.ofConv.toRingHom} := by
  let e := hopfBaseChangePointsEquiv (R := R) (F := F) (A := A) (K := K)
  let Y := e '' X
  letI : IsArtinianRing (F ⊗[R] A) := IsArtinianRing.of_finite F (F ⊗[R] A)
  letI : Finite (WithConv (F ⊗[R] A →ₐ[F] K)) := finiteFreeHopfPoints_finite
  have hY : ∀ (g : K ≃ₐ[F] K) (p : WithConv (F ⊗[R] A →ₐ[F] K)),
      p ∈ Y → commutativeHopfPointsAutomorphism g p ∈ Y := by
    rintro g p ⟨q, hq, rfl⟩
    exact ⟨_, hX g q hq, hopfBaseChangePointsEquiv_galois g q⟩
  have hc := hopfGaloisStablePointSet_eq_vanishing Y hY
  ext p
  constructor
  · intro hp a ha
    exact (hopfPointsVanishingIdeal_mem_iff X a).mp ha ⟨p, hp⟩
  · intro hp
    have hep : e p ∈ Y := by
      rw [hc]
      intro z hz
      obtain ⟨⟨a, s⟩, hs⟩ :=
        IsLocalizedModule.surj R⁰ (TensorProduct.mk R F A 1) z
      have heval (q : WithConv (A →ₐ[R] K)) :
          q a = (s : R) • e q z := by
        calc
          q a = e q (1 ⊗ₜ[R] a) := (algebraBaseChangePoint_original q.ofConv a).symm
          _ = e q ((s : R) • z) := congrArg (e q) hs.symm
          _ = (s : R) • e q z := ((e q).ofConv.toLinearMap.restrictScalars R).map_smul _ _
      have ha : a ∈ hopfPointsVanishingIdeal X := by
        apply (hopfPointsVanishingIdeal_mem_iff X a).mpr
        intro q
        rw [heval]
        have hqz := (hopfPointsVanishingIdeal_mem_iff Y z).mp hz
          ⟨e q.val, ⟨q.val, q.property, rfl⟩⟩
        rw [hqz, smul_zero]
      have hsK : IsUnit (algebraMap R K (s : R)) := by
        rw [IsScalarTower.algebraMap_apply R F K]
        exact (IsLocalization.map_units F s).map (algebraMap F K)
      change e p z = 0
      apply hsK.mul_left_cancel
      rw [mul_zero, ← Algebra.smul_def, ← heval]
      exact hp ha
    obtain ⟨q, hq, heq⟩ := hep
    exact e.injective heq ▸ hq

end
end Dubon2026
