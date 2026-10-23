import Dubon2026.SourceCurveGeneratorOrders
import Dubon2026.SourceCurveTateInverse

/-! The local residue of a power of a rational generator is its signed
order exactly for exponent minus one, and zero otherwise. The existing
principal-degree sum cancels these contributions globally. This is the
characteristic-free generator calculation for DUB-17/18 global residues. -/

noncomputable section

namespace Dubon2026.SourceCurve

open IntermediateField

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]

/-- The exact local power residue of an actual rational generator. -/
theorem generator_tateResidue_zpow (t : F) (ht : Transcendental K t)
    (hgen : K⟮t⟯ = ⊤) (v : Place K F) (n : ℤ) :
    v.tateResidue (t ^ n) t = if n = -1 then (v.ord t : K) else 0 := by
  obtain ⟨hfinite, _⟩ := finite_separable_of_adjoin_eq_top t hgen
  have hres := (place_residue_bijective_of_finite_coordinate t v).surjective
  rcases ord_generator_cases t ht hgen v with hv | hv | hv
  · rw [v.tateResidue_pole_parameter_zpow hres hv]
    simp only [hv, Int.cast_neg, Int.cast_one]
  · rw [v.tateResidue_unit_zpow hres hv]
    simp only [hv, Int.cast_zero, ite_self]
  · rw [v.tateResidue_parameter_zpow hv hres]
    simp only [hv, Int.cast_one]

/-- The signed orders of an actual rational generator sum to zero in the constant field. -/
theorem sum_generator_orders_cast (t : F) (ht : Transcendental K t)
    (hgen : K⟮t⟯ = ⊤) : (∑ᶠ v : Place K F, (v.ord t : K)) = 0 := by
  obtain ⟨hfinite, hsep⟩ := finite_separable_of_adjoin_eq_top t hgen
  have hr (v : Place K F) : Module.finrank K v.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (place_residue_bijective_of_finite_coordinate t v)
  have hs : (∑ᶠ v : Place K F, v.ord t) = 0 := by
    simpa only [hr, Nat.cast_one, mul_one] using sum_orders_eq_zero_of_separating_coordinate t ht
  have hf : (Function.support (fun v : Place K F => v.ord t)).Finite :=
    finite_function_support_of_separating_coordinate t ht t
  have h := (Int.castAddHom K).map_finsum hf
  rw [hs, map_zero] at h
  exact h.symm

/-- Every integer power of the rational generator has zero global residue against it. -/
theorem sum_generator_tateResidue_zpow (t : F) (ht : Transcendental K t)
    (hgen : K⟮t⟯ = ⊤) (n : ℤ) :
    (∑ᶠ v : Place K F, v.tateResidue (t ^ n) t) = 0 := by
  simp_rw [generator_tateResidue_zpow t ht hgen]
  by_cases hn : n = -1
  · simp only [hn, ite_true]
    exact sum_generator_orders_cast t ht hgen
  · simp only [if_neg hn, finsum_zero]

end Dubon2026.SourceCurve
