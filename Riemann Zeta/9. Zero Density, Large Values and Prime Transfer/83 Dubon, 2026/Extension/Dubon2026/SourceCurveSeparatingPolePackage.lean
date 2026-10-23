import Dubon2026.SourceCurveSeparatingPoleDegree
import Dubon2026.SourceCurvePolePackage

/-! DUB-17/18 -> good reduction -> residue genus maximum. Reuse the
existing integral coordinate basis and common pole bound verbatim. Only the
degree step needs the already proved separating-coordinate formula, so the
actual pole package is constructed in positive characteristic without
developing inseparable coordinates or a new Riemann--Roch theory. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

theorem exists_poleDivisorPackage_of_separating_coordinate
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (t : F) (ht : Transcendental K t) [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F]
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
  · rw [degree_poleDivisor_eq_finrank_separating t ht hf, hd]
  · have hlin := linearIndependent_coordinate_powers_mul (K := K)
      (RatFunc.transcendental_X (K := K)) hu
    simpa only [he] using hlin

end
end Dubon2026.SourceCurve
