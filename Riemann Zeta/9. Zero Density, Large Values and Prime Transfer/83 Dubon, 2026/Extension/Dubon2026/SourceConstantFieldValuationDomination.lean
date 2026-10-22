import Dubon2026.SourceConstantFieldLocalRing
import Mathlib.RingTheory.Valuation.LocalSubring

/-! DUB-17/18 -> Qbar torsion comparison -> original place extension.
A proper uniformizer ideal in the scalar-extended local ring yields a valuation
ring whose inverse image is exactly the original local ring. Separate this
native domination calculation from the concrete coefficient-independence
argument, so both are checked at unchanged proof limits.
Adapted from S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section

variable {K F K' : Type*} (F' : Type*) [Field K] [Field F] [Field K'] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F']
  {ι : Type*} (B : Module.Basis ι K K') (P : Place K F)

theorem exists_extending_valuation_of_proper_ideal {π : P.toValuationSubring}
    (hπ : Irreducible π)
    (hI : Ideal.span {(⟨algebraMap F F' (π : F), algebraMap_coe_mem_rangePsi F' B P π⟩ :
      rangePsi F' B P)} ≠ ⊤) :
    ∃ V : ValuationSubring F', V ≠ ⊤ ∧
      (∀ c : K', algebraMap K' F' c ∈ V) ∧
      V.comap (algebraMap F F') = P.toValuationSubring := by
  have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hπA : algebraMap F F' (π : F) ∈ rangePsi F' B P := algebraMap_coe_mem_rangePsi F' B P π
  obtain ⟨V, hAV, hIV⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  have hAV' : ∀ y, y ∈ rangePsi F' B P → y ∈ V := fun y hy => hAV hy
  have hπV : algebraMap F F' (π : F) ∈ V := hAV' _ hπA
  have hnu : algebraMap F F' (π : F) ∈ V.nonunits :=
    hIV ⟨⟨_, hπA⟩, Ideal.mem_span_singleton_self _, rfl⟩
  have hπVinv : (algebraMap F F' (π : F))⁻¹ ∉ V := by
    have := (V.inv_mem_nonunits_iff (x := (algebraMap F F' (π : F))⁻¹)).1
      (by rw [inv_inv]; exact hnu)
    exact this.resolve_left (inv_ne_zero ((map_ne_zero _).2 hπ0))

  have hover : V.comap (algebraMap F F') = P.toValuationSubring := by
    ext f
    rw [ValuationSubring.mem_comap]
    refine ⟨fun hfV => ?_, fun hf => hAV' _ (algebraMap_coe_mem_rangePsi F' B P ⟨f, hf⟩)⟩
    by_contra hfO
    have hf0 : f ≠ 0 := by rintro rfl; exact hfO (zero_mem _)
    have hn : P.ord f < 0 := by
      by_contra h
      push Not at h
      exact hfO ((P.mem_iff_ord_nonneg (f := f)).2 h)
    obtain ⟨u, hu⟩ := P.exists_unit_mul_zpow hf0 hπ
    have hui : (((u⁻¹ : P.toValuationSubringˣ) : P.toValuationSubring) : F) *
        ((u : P.toValuationSubring) : F) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one]
    set n := P.ord f with hn'
    have key : (π : F)⁻¹ = (((u⁻¹ : P.toValuationSubringˣ) : P.toValuationSubring) : F) * f *
        (π : F) ^ ((-n - 1).toNat) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
      conv_rhs => rw [hu]
      calc (π : F)⁻¹ = 1 * ((π : F) ^ n * (π : F) ^ (-n - 1)) := by
            rw [← zpow_add₀ hπ0, show n + (-n - 1) = -1 by ring, zpow_neg_one, one_mul]
        _ = _ := by rw [← hui]; ring
    apply hπVinv
    rw [← map_inv₀, key, map_mul, map_mul, map_pow]
    exact mul_mem (mul_mem (hAV' _ (algebraMap_coe_mem_rangePsi F' B P _)) hfV) (pow_mem hπV _)
  refine ⟨V, ?_, fun c => hAV' _ (algebraMap_mem_rangePsi F' B P c), hover⟩
  intro hV
  exact hπVinv (hV ▸ ValuationSubring.mem_top _)

end
end Dubon2026.SourceCurve.ConstantField
