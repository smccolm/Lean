import Dubon2026.LocalFieldIntegerIntegralClosure

/-! # Uniqueness of the actual extending local valuative relation -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

/-- On a field the actual valuation-ring membership relation determines
the entire valuative relation, by division by a nonzero denominator. -/
theorem valuativeRel_eq_of_unitBall_eq {L : Type*} [Field L]
    (v w : ValuativeRel L) (h : ∀ x, v.vle x 1 ↔ w.vle x 1) : v = w := by
  apply ValuativeRel.ext
  funext x y
  apply propext
  by_cases hy : y = 0
  · subst y
    have hv : v.vle x 0 ↔ x = 0 := by
      letI := v
      exact ValuativeRel.vle_zero_iff
    have hw : w.vle x 0 ↔ x = 0 := by
      letI := w
      exact ValuativeRel.vle_zero_iff
    exact hv.trans hw.symm
  · have hv : v.vle (x / y) 1 ↔ v.vle x y := by
      letI := v
      exact ValuativeRel.div_vle_one_iff hy
    have hw : w.vle (x / y) 1 ↔ w.vle x y := by
      letI := w
      exact ValuativeRel.div_vle_one_iff hy
    exact hv.symm.trans ((h (x / y)).trans hw)

/-- The original extension valuation ring is characterized by
integrality over the original base integer ring. -/
theorem localField_vle_one_iff_integral
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] (x : L) :
    x ≤ᵥ 1 ↔ IsIntegral 𝒪[K] x := by
  haveI : IsIntegralClosure 𝒪[L] 𝒪[K] L := localField_integer_isIntegralClosure
  rw [IsIntegralClosure.isIntegral_iff (A := 𝒪[L])]
  constructor
  · intro hx
    exact ⟨⟨x, (Valuation.vle_one_iff (ValuativeRel.valuation L)).mp hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact (Valuation.vle_one_iff (ValuativeRel.valuation L)).mpr y.property

/-- Two actual local valuations extending the same original local
field agree, even when their topological structures were constructed separately.
Both integer rings are the original integral closure. -/
theorem localField_valuative_extension_unique
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (v w : ValuativeRel L) (t u : TopologicalSpace L)
    (hv : letI := v; letI := t; IsNonarchimedeanLocalField L)
    (hw : letI := w; letI := u; IsNonarchimedeanLocalField L)
    (hvext : letI := v;
      (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L))
    (hwext : letI := w;
      (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)) : v = w := by
  apply valuativeRel_eq_of_unitBall_eq
  intro x
  have hvi : v.vle x 1 ↔ IsIntegral 𝒪[K] x := by
    letI := v
    letI := t
    haveI := hv
    haveI := hvext
    exact localField_vle_one_iff_integral K L x
  have hwi : w.vle x 1 ↔ IsIntegral 𝒪[K] x := by
    letI := w
    letI := u
    haveI := hw
    haveI := hwext
    exact localField_vle_one_iff_integral K L x
  exact hvi.trans hwi.symm

end
end Dubon2026
