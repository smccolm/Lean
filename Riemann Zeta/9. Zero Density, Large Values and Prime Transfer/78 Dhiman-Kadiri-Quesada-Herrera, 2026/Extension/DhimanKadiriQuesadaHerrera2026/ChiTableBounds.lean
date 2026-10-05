import DhimanKadiriQuesadaHerrera2026.AFETableThree

namespace DhimanKadiriQuesadaHerrera2026

/-- A rational polynomial enclosure for C₁ retains all signs on the closed source strip. -/
theorem chiC1_le_rational_polynomial {σ t₀ P Q T : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (hP : 0 < P) (hPpi : P ≤ Real.pi)
    (hpiQ : Real.pi ≤ Q) (hT : 0 < T) (hTt : T ≤ t₀) :
    chiC1 σ t₀ ≤ (1 - σ) ^ 2 * (1 / 2 + 2 / P) +
      (1 - σ) * (σ - 1 / 2) * ((Q / 2) ^ 2 + (1 - σ) / (2 * T)) := by
  have hs : 0 ≤ 1 - σ := by linarith [hσ.2]
  have hs' : 0 ≤ σ - 1 / 2 := by linarith [hσ.1]
  unfold chiC1
  gcongr

/-- A concave cubic is bounded globally on the positive ray by two explicit squares. -/
theorem cubic_le_rational_majorant {a A B R c : ℝ} (ha : 0 ≤ a) (hB : 0 < B)
    (hR : 0 ≤ R) (hc : 0 ≤ c) :
    A * a - B * a ^ 2 - R * a ^ 3 ≤ 2 * R * c ^ 3 + (A - 3 * R * c ^ 2) ^ 2 / (4 * B) := by
  have hsq := mul_nonneg hB.le (sq_nonneg (a - (A - 3 * R * c ^ 2) / (2 * B)))
  have hcube := mul_nonneg hR (mul_nonneg (sq_nonneg (a - c)) (by positivity : 0 ≤ a + 2 * c))
  have he : 2 * R * c ^ 3 + (A - 3 * R * c ^ 2) ^ 2 / (4 * B) -
      (A * a - B * a ^ 2 - R * a ^ 3) =
      B * (a - (A - 3 * R * c ^ 2) / (2 * B)) ^ 2 + R * ((a - c) ^ 2 * (a + 2 * c)) := by
    field_simp
    ring
  linarith

/-- The cubic formula yields an exact rational global certificate for the actual C₁. -/
theorem chiC1_le_rational_certificate {σ t₀ P Q T c C : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (hP : 0 < P) (hPpi : P ≤ Real.pi)
    (hpiQ : Real.pi ≤ Q) (hT : 0 < T) (hTt : T ≤ t₀) (hc : 0 ≤ c)
    (hB : 0 < Q ^ 2 / 4 - 1 / 2 - 2 / P - 1 / (4 * T))
    (hcert : 2 * (1 / (2 * T)) * c ^ 3 +
      (Q ^ 2 / 8 - 3 * (1 / (2 * T)) * c ^ 2) ^ 2 /
        (4 * (Q ^ 2 / 4 - 1 / 2 - 2 / P - 1 / (4 * T))) ≤ C) : chiC1 σ t₀ ≤ C := by
  have h := chiC1_le_rational_polynomial hσ hP hPpi hpiQ hT hTt
  have hpoly := cubic_le_rational_majorant (a := 1 - σ) (A := Q ^ 2 / 8)
    (B := Q ^ 2 / 4 - 1 / 2 - 2 / P - 1 / (4 * T)) (R := 1 / (2 * T)) (c := c)
    (by linarith [hσ.2]) hB (by positivity) hc
  have he : (1 - σ) ^ 2 * (1 / 2 + 2 / P) +
      (1 - σ) * (σ - 1 / 2) * ((Q / 2) ^ 2 + (1 - σ) / (2 * T)) =
      Q ^ 2 / 8 * (1 - σ) - (Q ^ 2 / 4 - 1 / 2 - 2 / P - 1 / (4 * T)) * (1 - σ) ^ 2 -
        (1 / (2 * T)) * (1 - σ) ^ 3 := by ring
  rw [he] at h
  exact h.trans (hpoly.trans hcert)

/-- The actual C₁ maximum at the two pi threshold has a rational certificate. -/
theorem chiC1_le_two_pi_table {σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    chiC1 σ (2 * Real.pi) ≤ 17911633 / 62500000 := by
  apply chiC1_le_rational_certificate hσ (P := 314159265358979323846 / 100000000000000000000)
    (Q := 314159265358979323847 / 100000000000000000000) (T := 2 * (314159265358979323846 / 100000000000000000000))
    (c := 458383421 / 1000000000) (by norm_num) (by linarith [Real.pi_gt_d20])
    (by linarith [Real.pi_lt_d20]) (by norm_num) (by linarith [Real.pi_gt_d20])
    (by norm_num) (by norm_num)
  norm_num

/-- The actual C₁ maximum at the thousand threshold has a rational certificate. -/
theorem chiC1_le_thousand_table {σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    chiC1 σ (1000) ≤ 285929379 / 1000000000 := by
  apply chiC1_le_rational_certificate hσ (P := 314159265358979323846 / 100000000000000000000)
    (Q := 314159265358979323847 / 100000000000000000000) (T := 1000)
    (c := 28968181 / 62500000) (by norm_num) (by linarith [Real.pi_gt_d20])
    (by linarith [Real.pi_lt_d20]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num

/-- The actual C₁ maximum at the large threshold has a rational certificate. -/
theorem chiC1_le_large_table {σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    chiC1 σ (10000000000) ≤ 285925459 / 1000000000 := by
  apply chiC1_le_rational_certificate hσ (P := 314159265358979323846 / 100000000000000000000)
    (Q := 314159265358979323847 / 100000000000000000000) (T := 10000000000)
    (c := 92704979 / 200000000) (by norm_num) (by linarith [Real.pi_gt_d20])
    (by linarith [Real.pi_lt_d20]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num

/-- The actual C₁ maximum at the trillion threshold has a rational certificate. -/
theorem chiC1_le_trillion_table {σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    chiC1 σ (3000000000000) ≤ 285925459 / 1000000000 := by
  apply chiC1_le_rational_certificate hσ (P := 314159265358979323846 / 100000000000000000000)
    (Q := 314159265358979323847 / 100000000000000000000) (T := 3000000000000)
    (c := 92704979 / 200000000) (by norm_num) (by linarith [Real.pi_gt_d20])
    (by linarith [Real.pi_lt_d20]) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num


/-- A sixth-order exponential enclosure with its proved remainder. -/
theorem exp_le_table_taylor {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    Real.exp v ≤ 1 + v + v ^ 2 / 2 + v ^ 3 / 6 + v ^ 4 / 24 + v ^ 5 / 120 + 7 * v ^ 6 / 4320 := by
  have h := Real.exp_bound' hv hv1 (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The exact lowest source height has a small exponential tail certified by a finite series. -/
theorem exp_neg_two_pi_table : Real.exp (-Real.pi * (2 * Real.pi)) ≤ 3 / 1000000000 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 197 / 10) 64
  norm_num [Finset.sum_range_succ] at h
  have hbase : (1000000000 / 3 : ℝ) ≤ Real.exp (197 / 10) := by linarith
  have harg : (197 / 10 : ℝ) ≤ Real.pi * (2 * Real.pi) := by nlinarith [Real.pi_gt_d2]
  have he := hbase.trans (Real.exp_le_exp.mpr harg)
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000000000 / 3) he
  rw [neg_mul, Real.exp_neg]
  norm_num at hi
  exact hi

/-- The remaining source heights have an exponential tail below 10⁻³⁰. -/
theorem exp_neg_large_table {t₀ : ℝ} (ht : 1000 ≤ t₀) :
    Real.exp (-Real.pi * t₀) ≤ 1 / 1000000000000000000000000000000 := by
  have htpos : 0 < t₀ := by linarith
  have hp : (3000 : ℝ) ≤ Real.pi * t₀ := by nlinarith [Real.pi_gt_three]
  have hn : (1000000000000000000000000000000 : ℝ) ≤ (3000 : ℝ) ^ 20 / (Nat.factorial 20 : ℝ) := by norm_num
  have hpow : (3000 : ℝ) ^ 20 / (Nat.factorial 20 : ℝ) ≤
      (Real.pi * t₀) ^ 20 / (Nat.factorial 20 : ℝ) := by gcongr
  have he := hn.trans (hpow.trans (Real.pow_div_factorial_le_exp (Real.pi * t₀) (by positivity) 20))
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000000000000000000000000000000) he
  rw [neg_mul, Real.exp_neg]
  simpa only [one_div] using hi

/-- Explicit C₁, exponential-tail and threshold bounds certify the full C₀ product. -/
theorem chiC0_le_table_certificate {σ t₀ T C E D : ℝ}
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) (hT : 0 < T) (hTt : T ≤ t₀)
    (hC : chiC1 σ t₀ ≤ C) (hE : Real.exp (-Real.pi * t₀) ≤ E)
    (hv : 1 / (12 * T) + 1 / (90 * T ^ 3) ≤ 1)
    (hcert : let v := 1 / (12 * T) + 1 / (90 * T ^ 3)
      (1 + v + v ^ 2 / 2 + v ^ 3 / 6 + v ^ 4 / 24 + v ^ 5 / 120 + 7 * v ^ 6 / 4320) *
        (1 + E) * (1 + C / T) ≤ 1 + D) : chiC0 σ t₀ ≤ 1 + D := by
  have ht : 0 < t₀ := hT.trans_le hTt
  have hc0 := chiC1_nonneg hσ ht
  have hC0 : 0 ≤ C := hc0.trans hC
  have hE0 : 0 ≤ E := (Real.exp_pos _).le.trans hE
  have harg : 1 / (12 * t₀) + 1 / (90 * t₀ ^ 3) ≤ 1 / (12 * T) + 1 / (90 * T ^ 3) := by gcongr
  have he := (Real.exp_le_exp.mpr harg).trans (exp_le_table_taylor (by positivity) hv)
  rw [chiC0_eq ht]
  apply le_trans _ hcert
  dsimp only
  gcongr
  exact he

/-- The complete C₀ has an outward certificate at the two pi threshold. -/
theorem chiC0_le_two_pi_table {σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    chiC0 σ (2 * Real.pi) ≤ 1 + 596193 / 10000000 := by
  apply chiC0_le_table_certificate hσ (T := 2 * (314159265358979323846 / 100000000000000000000))
    (C := 17911633 / 62500000) (E := 3 / 1000000000)
    (by norm_num) (by linarith [Real.pi_gt_d20])
    (chiC1_le_two_pi_table hσ) (exp_neg_two_pi_table)
    (by norm_num)
  norm_num

/-- The complete C₀ has an outward certificate at the thousand threshold. -/
theorem chiC0_le_thousand_table {σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    chiC0 σ (1000) ≤ 1 + 3692901 / 10000000000 := by
  apply chiC0_le_table_certificate hσ (T := 1000)
    (C := 285929379 / 1000000000) (E := 1 / 1000000000000000000000000000000)
    (by norm_num) (by norm_num)
    (chiC1_le_thousand_table hσ) (exp_neg_large_table (by norm_num))
    (by norm_num)
  norm_num

/-- The complete C₀ has an outward certificate at the large threshold. -/
theorem chiC0_le_large_table {σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    chiC0 σ (10000000000) ≤ 1 + 923147 / 25000000000000000 := by
  apply chiC0_le_table_certificate hσ (T := 10000000000)
    (C := 285925459 / 1000000000) (E := 1 / 1000000000000000000000000000000)
    (by norm_num) (by norm_num)
    (chiC1_le_large_table hσ) (exp_neg_large_table (by norm_num))
    (by norm_num)
  norm_num

/-- The complete C₀ has an outward certificate at the trillion threshold. -/
theorem chiC0_le_trillion_table {σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 1) :
    chiC0 σ (3000000000000) ≤ 1 + 1230863 / 10000000000000000000 := by
  apply chiC0_le_table_certificate hσ (T := 3000000000000)
    (C := 285925459 / 1000000000) (E := 1 / 1000000000000000000000000000000)
    (by norm_num) (by norm_num)
    (chiC1_le_trillion_table hσ) (exp_neg_large_table (by norm_num))
    (by norm_num)
  norm_num

/-- The actual global chi excess has the certified two pi table bound. -/
theorem afeDelta0_le_two_pi_table : afeDelta0 (2 * Real.pi) ≤ 596193 / 10000000 := by
  have hn : afeSigmaStrip.Nonempty := ⟨1, by norm_num [afeSigmaStrip]⟩
  have hs : sSup ((fun σ => chiC0 σ (2 * Real.pi)) '' afeSigmaStrip) ≤ 1 + 596193 / 10000000 := by
    apply csSup_le (hn.image _)
    rintro _ ⟨σ, hσ, rfl⟩
    exact chiC0_le_two_pi_table hσ
  dsimp only [afeDelta0]
  linarith

/-- The actual global chi excess has the certified thousand table bound. -/
theorem afeDelta0_le_thousand_table : afeDelta0 (1000) ≤ 3692901 / 10000000000 := by
  have hn : afeSigmaStrip.Nonempty := ⟨1, by norm_num [afeSigmaStrip]⟩
  have hs : sSup ((fun σ => chiC0 σ (1000)) '' afeSigmaStrip) ≤ 1 + 3692901 / 10000000000 := by
    apply csSup_le (hn.image _)
    rintro _ ⟨σ, hσ, rfl⟩
    exact chiC0_le_thousand_table hσ
  dsimp only [afeDelta0]
  linarith

/-- The actual global chi excess has the certified large table bound. -/
theorem afeDelta0_le_large_table : afeDelta0 (10000000000) ≤ 923147 / 25000000000000000 := by
  have hn : afeSigmaStrip.Nonempty := ⟨1, by norm_num [afeSigmaStrip]⟩
  have hs : sSup ((fun σ => chiC0 σ (10000000000)) '' afeSigmaStrip) ≤ 1 + 923147 / 25000000000000000 := by
    apply csSup_le (hn.image _)
    rintro _ ⟨σ, hσ, rfl⟩
    exact chiC0_le_large_table hσ
  dsimp only [afeDelta0]
  linarith

/-- The actual global chi excess has the certified trillion table bound. -/
theorem afeDelta0_le_trillion_table : afeDelta0 (3000000000000) ≤ 1230863 / 10000000000000000000 := by
  have hn : afeSigmaStrip.Nonempty := ⟨1, by norm_num [afeSigmaStrip]⟩
  have hs : sSup ((fun σ => chiC0 σ (3000000000000)) '' afeSigmaStrip) ≤ 1 + 1230863 / 10000000000000000000 := by
    apply csSup_le (hn.image _)
    rintro _ ⟨σ, hσ, rfl⟩
    exact chiC0_le_trillion_table hσ
  dsimp only [afeDelta0]
  linarith

end DhimanKadiriQuesadaHerrera2026
