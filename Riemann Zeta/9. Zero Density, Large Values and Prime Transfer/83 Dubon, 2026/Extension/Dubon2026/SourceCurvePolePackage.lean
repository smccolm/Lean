import Dubon2026.SourceCurveIntegralCoordinateBasis
import Dubon2026.SourceCurvePoleBasisBound

/-! DUB-17/18 -> original function-field Riemann--Roch -> a bounded global
index. The source pole-divisor package is constructed from a literal
transcendental coordinate: its actual pole divisor has the correct degree,
and a pinned integral basis supplies independent polynomial multiples with
a common pole bound. The package definition follows the selected
PoleDivisorPackage of S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. No package or genus-bound premise
is assumed by the constructor.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

/-- Concrete pole and independent-function data used to bound the global index. -/
structure PoleDivisorPackage (K F : Type*) [Field K] [Field F] [Algebra K F] where
  /-- The actual coordinate function. -/
  x : F
  /-- Its actual effective pole bound. -/
  B : Divisor K F
  /-- Effectivity of the bound. -/
  hB_eff : 0 ≤ B
  /-- The coordinate satisfies its pole bound. -/
  hx_mem : x ∈ LSpace B
  /-- The number of basis functions. -/
  n : ℕ
  /-- The field degree is positive. -/
  hn_pos : 0 < n
  /-- Pole degree equals the number of basis functions. -/
  degB_eq : Divisor.degree B = n
  /-- A common pole multiplier for the basis. -/
  c : ℕ
  /-- The actual field basis functions. -/
  u : Fin n → F
  /-- Every basis function satisfies the common pole bound. -/
  hu_mem : ∀ i, u i ∈ LSpace (c • B)
  /-- All polynomial-coordinate multiples are independent over the constants. -/
  lin_indep : LinearIndependent K (fun p : ℕ × Fin n => x ^ p.1 * u p.2)

theorem exists_poleDivisorPackage_of_finite_coordinate
    {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
    (t : F) (ht : Transcendental K t) [FiniteDimensional K⟮t⟯ F]
    (hf : {v : Place K F | v.ord t ≠ 0}.Finite) :
    Nonempty (PoleDivisorPackage K F) := by
  let e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc K) F :=
    ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
      (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K) =
        RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  letI : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have he : algebraMap (RatFunc K) F RatFunc.X = t := by
    show ((RatFunc.algEquivOfTranscendental t ht RatFunc.X : K⟮t⟯) : F) = t
    rw [RatFunc.algEquivOfTranscendental_X]
  have hd : Module.finrank K⟮t⟯ F = Module.finrank (RatFunc K) F :=
    Algebra.finrank_eq_of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  obtain ⟨u, hu, hreg⟩ := exists_basis_regular_outside_X (K := K) (F := F)
  have hr : ∀ i (v : Place K F), 0 ≤ v.ord t → 0 ≤ v.ord (u i) := by
    simpa only [he] using hreg
  obtain ⟨c, hc⟩ := exists_forall_mem_lSpace_nsmul_poleDivisor t hf u hr
  refine ⟨{
    x := t
    B := poleDivisor t hf
    hB_eff := poleDivisor_nonneg t hf
    hx_mem := mem_lSpace_poleDivisor t hf
    n := Module.finrank (RatFunc K) F
    hn_pos := Module.finrank_pos
    degB_eq := ?_
    c := c
    u := u
    hu_mem := hc
    lin_indep := ?_ }⟩
  · rw [degree_poleDivisor_eq_finrank t ht hf, hd]
  · have hlin := linearIndependent_coordinate_powers_mul (K := K)
      (RatFunc.transcendental_X (K := K)) hu
    simpa only [he] using hlin

end
end Dubon2026.SourceCurve
