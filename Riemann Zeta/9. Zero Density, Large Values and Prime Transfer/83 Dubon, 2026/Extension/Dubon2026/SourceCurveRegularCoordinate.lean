import Dubon2026.SourceCurveIntegralDerivatives

/-! DUB-17/18 -> canonical-divisor finiteness. At an unramified chart
point the coordinate differential spans the integral local module. The
already proved integral uniformizer generation then shows that its literal
local differential order is zero. The finite different ideal will bound the
exceptional points in the actual original-field consumer.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open Polynomial KaehlerDifferential
open scoped TensorProduct

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem span_D_coordinate_of_formallyUnramified
    [Algebra K[X] v.toValuationSubring] [IsScalarTower K K[X] v.toValuationSubring]
    [Algebra.FormallyUnramified K[X] v.toValuationSubring] :
    Submodule.span v.toValuationSubring
      {D K v.toValuationSubring (algebraMap K[X] v.toValuationSubring X)} = ⊤ := by
  have hrange : LinearMap.range (KaehlerDifferential.mapBaseChange K K[X] v.toValuationSubring) = ⊤ := by
    rw [KaehlerDifferential.range_mapBaseChange]
    exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)
  apply top_le_iff.mp
  rw [← hrange]
  rintro _ ⟨t, rfl⟩
  induction t with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul b ω =>
    rw [KaehlerDifferential.mapBaseChange_tmul,
      show ω = (KaehlerDifferential.polynomialEquiv K ω) • D K K[X] X from
        ((KaehlerDifferential.polynomialEquiv K).symm_apply_apply ω).symm.trans
          (KaehlerDifferential.polynomialEquiv_symm K _),
      LinearMap.map_smul, KaehlerDifferential.map_D]
    apply Submodule.smul_mem _ b
    have hD := Submodule.mem_span_singleton_self
      (R := v.toValuationSubring) (D K v.toValuationSubring
        (algebraMap K[X] v.toValuationSubring X))
    have hq := Submodule.smul_mem
      (Submodule.span v.toValuationSubring
        {D K v.toValuationSubring (algebraMap K[X] v.toValuationSubring X)})
      (algebraMap K[X] v.toValuationSubring (KaehlerDifferential.polynomialEquiv K ω)) hD
    simpa only [algebraMap_smul] using hq

theorem ordDifferential_D_eq_zero_of_integral_span
    [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
    [Algebra.IsSeparable K v.ResidueField] [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (t : v.toValuationSubring)
    (ht : Submodule.span v.toValuationSubring {D K v.toValuationSubring t} = ⊤) :
    v.ordDifferential (D K F (t : F)) = 0 := by
  obtain ⟨b, hbmem, hb⟩ := v.exists_integral_D_eq_smul_dCoord t.2
  have hπmem : D K v.toValuationSubring v.uniformizerSubring ∈
      Submodule.span v.toValuationSubring {D K v.toValuationSubring t} := by
    rw [ht]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hπmem
  have hpush := congrArg (KaehlerDifferential.map K K v.toValuationSubring F) ha
  rw [map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D] at hpush
  have haF : (a : F) • D K F (t : F) = v.dCoord :=
    (algebraMap_smul F a (D K F (t : F))).trans hpush
  have hzero : ((a : F) * b - 1) • v.dCoord = 0 := by
    rw [sub_smul, one_smul, mul_smul, ← hb, haF, sub_self]
  have hab : (a : F) * b = 1 :=
    sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right v.dCoord_ne_zero)
  have ha0 : (a : F) ≠ 0 := by intro h; simp [h] at hab
  have hb0 : b ≠ 0 := by intro h; simp [h] at hab
  have hsum := congrArg v.ord hab
  rw [v.ord_mul ha0 hb0, v.ord_one] at hsum
  have hna := v.ord_nonneg_of_mem a.2
  have hnb := v.ord_nonneg_of_mem hbmem
  change v.ord (v.differentialCoeff (D K F (t : F))) = 0
  rw [v.differentialCoeff_unique hb]
  omega

end
end Dubon2026.SourceCurve.Place
