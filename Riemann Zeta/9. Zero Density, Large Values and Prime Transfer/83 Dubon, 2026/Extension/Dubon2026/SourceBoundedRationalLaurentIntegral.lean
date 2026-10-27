import Dubon2026.SourceBoundedRationalLaurentImage

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field -> bounded rational Fourier denominators. Clear only
the finitely many integer coefficient bounds in the original Laurent monic
relation. Native Laurent normality then combines that relation with the
independent bounded-fraction premise. No new pole-clearing exponents occur.
The finite scaling calculation adapts `exists_int_multiple` from
anthropics/fermats-last-theorem at 6e837e75355538c7f80bab5b956861e86c4eacc2,
Apache License 2.0. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem hasBoundedIntegralLaurentCoefficients_of_monic_relation_of_bounded_fraction
    {d : ℕ} (y : LaurentSeries ℚ) (a : Fin d → LaurentSeries ℚ)
    (ha : ∀ i, HasBoundedIntegralLaurentCoefficients (a i))
    (hrel : y ^ d + ∑ i : Fin d, a i * y ^ (i : ℕ) = 0)
    (h u : LaurentSeries ℚ) (hh0 : h ≠ 0)
    (hh : HasBoundedIntegralLaurentCoefficients h)
    (hu : HasBoundedIntegralLaurentCoefficients u) (hhy : h * y = u) :
    HasBoundedIntegralLaurentCoefficients y := by
  classical
  letI : CharZero (LaurentSeries ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (LaurentSeries ℚ)).injective
  letI : CharZero (LaurentSeries ℤ) :=
    charZero_of_injective_algebraMap
      (show Function.Injective (algebraMap ℤ (LaurentSeries ℤ)) from by
        rw [show algebraMap ℤ (LaurentSeries ℤ) = HahnSeries.C from RingHom.ext_int _ _]
        exact HahnSeries.C_injective)
  choose D A hD hA using fun i => (ha i).exists_integer_series
  obtain ⟨Dh, H, hDh, hH⟩ := hh.exists_integer_series
  obtain ⟨Du, U, hDu, hU⟩ := hu.exists_integer_series
  let c : ℤ := ∏ i, D i
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hD i
  let z : Fin d → ℤ := fun i => c ^ (d - 1 - i) * ∏ j ∈ Finset.univ.erase i, D j
  have hzid : ∀ i : Fin d, z i * D i * c ^ (i : ℕ) = c ^ d := by
    intro i
    have h1 : (∏ j ∈ Finset.univ.erase i, D j) * D i = c :=
      Finset.prod_erase_mul _ _ (Finset.mem_univ i)
    have h2 : d - 1 - (i : ℕ) + 1 + i = d := by have := i.2; omega
    calc z i * D i * c ^ (i : ℕ) =
        c ^ (d - 1 - i) * ((∏ j ∈ Finset.univ.erase i, D j) * D i) * c ^ (i : ℕ) := by
          dsimp [z]; ring
      _ = c ^ (d - 1 - i) * c * c ^ (i : ℕ) := by rw [h1]
      _ = c ^ (d - 1 - (i : ℕ) + 1 + i) := by rw [pow_add, pow_succ]
      _ = c ^ d := by rw [h2]
  let ι : LaurentSeries ℤ →+* LaurentSeries ℚ := coeffMap (algebraMap ℤ ℚ)
  let b : Fin d → LaurentSeries ℤ := fun i => (z i : LaurentSeries ℤ) * A i
  let P : Polynomial (LaurentSeries ℤ) :=
    Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ)
  have hP : P.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt b)
  let g : LaurentSeries ℚ := (c : LaurentSeries ℚ) * y
  have hib : ∀ i, ι (b i) = (z i : LaurentSeries ℚ) * D i * a i := by
    intro i
    change ι ((z i : LaurentSeries ℤ) * A i) = _
    rw [map_mul, hA i, map_intCast]
    ring
  have hroot : Polynomial.eval₂ ι g P = 0 := by
    change Polynomial.eval₂ ι g
      (Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ)) = 0
    rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, hib]
    have hterm : ∀ i : Fin d, (z i : LaurentSeries ℚ) * D i * a i * g ^ (i : ℕ) =
        (c : LaurentSeries ℚ) ^ d * (a i * y ^ (i : ℕ)) := by
      intro i
      have hnum : (z i : LaurentSeries ℚ) * D i * (c : LaurentSeries ℚ) ^ (i : ℕ) =
          (c : LaurentSeries ℚ) ^ d := by exact_mod_cast hzid i
      rw [show g = (c : LaurentSeries ℚ) * y from rfl, mul_pow, ← hnum]
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum,
      show g ^ d = (c : LaurentSeries ℚ) ^ d * y ^ d from mul_pow _ _ _,
      ← mul_add, hrel, mul_zero]
  let hZ : LaurentSeries ℤ := (Du : LaurentSeries ℤ) * H
  have hH0 : H ≠ 0 := by
    intro hz
    have he : (Dh : LaurentSeries ℚ) * h = 0 := by rw [← hH, hz, map_zero]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hDh) hh0 he
  have hhZ0 : hZ ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hDu) hH0
  have hmul : ι hZ * g ∈ ι.range := by
    refine ⟨(c * Dh : ℤ) * U, ?_⟩
    change ι (((c * Dh : ℤ) : LaurentSeries ℤ) * U) = ι ((Du : LaurentSeries ℤ) * H) * g
    rw [map_mul ι, map_mul ι, hU, hH]
    simp only [map_intCast, Int.cast_mul, map_mul]
    rw [← hhy]
    dsimp [g]
    ring
  obtain ⟨G, hG⟩ := rationalLaurentSeries_mem_integer_image_of_monic_of_fraction
    g P hP hroot hZ hhZ0 hmul
  exact hasBoundedIntegralLaurentCoefficients_of_integer_series c hc0 G hG

end
end Dubon2026.SourceFunctionField
