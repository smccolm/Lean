import RiemannZeta.GuthMaynard.LargeValuesAffineIteration

open Complex Finset Filter FourierTransform MeasureTheory Real Set
open scoped ComplexConjugate ContDiff FourierTransform Topology

namespace RiemannZeta.GuthMaynard

example
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q Y xi : ℝ} (hY : 0 ≤ Y) (hxi : |xi| ≤ Y) :
    ∑ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
        ‖gmAffineFirstPoissonPairTerm f M₂ M₃ hM₃ xi p‖ ^ 2 =
      ∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
          gmAffineRetainedFirstPoissonPairSquare
            f Q M₂ M₃ hM₃ (m₁, ell) xi := by
  rw [sum_gmAffineFirstPoissonPairTerm_sq_eq_tsum_retained]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  rw [tsum_eq_sum (s := gmAffineFirstPoissonEllRange M₁ M₃ Q Y)]
  intro ell hell
  unfold gmAffineRetainedFirstPoissonPairSquare
  rw [if_neg]
  intro htau
  apply hell
  apply mem_gmAffineFirstPoissonEllRange_of_pair
    (Q := Q) (p := (m₁, ell)) hM₁ hM₃ hY hxi
  exact mem_gmAffineFirstPoissonPairs.mpr
    ⟨hm₁, (mem_gmAffinePoissonNearSet_iff_firstPoissonTau hM₃).mpr htau⟩

noncomputable def testRadius (M₁ M₃ : ℕ) (Q : ℝ) : ℝ :=
  Q * (2 * M₁ : ℝ) / (8 * M₃ : ℝ)

example {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q) {p : ℤ × ℤ}
    (hp : p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi) :
    |xi + ((p.1 * p.2 : ℤ) : ℝ)| < testRadius M₁ M₃ Q := by
  obtain ⟨hm₁, hell⟩ := mem_gmAffineFirstPoissonPairs.mp hp
  have hm₁neZ : p.1 ≠ 0 := gmAffineSignedShell_ne_zero hM₁ hm₁
  have hm₁neR : (p.1 : ℝ) ≠ 0 := by exact_mod_cast hm₁neZ
  have hnear : |(8 * M₃ : ℝ) * (xi / (p.1 : ℝ) + (p.2 : ℝ))| < Q := by
    unfold gmAffinePoissonNearSet at hell
    exact (Finset.mem_filter.mp hell).2
  have hrewrite : xi / (p.1 : ℝ) + (p.2 : ℝ) =
      (xi + (p.1 : ℝ) * (p.2 : ℝ)) / (p.1 : ℝ) := by
    field_simp [hm₁neR]
  rw [hrewrite, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 8 * M₃),
    abs_div] at hnear
  have hmabs : 0 < |(p.1 : ℝ)| := abs_pos.mpr hm₁neR
  have hscale : (0 : ℝ) < 8 * M₃ := by positivity
  have hdiv : |xi + (p.1 : ℝ) * (p.2 : ℝ)| / |(p.1 : ℝ)| <
      Q / (8 * M₃ : ℝ) := by
    rw [lt_div_iff₀ hscale]
    simpa only [mul_comm] using hnear
  have hmul : |xi + (p.1 : ℝ) * (p.2 : ℝ)| <
      (Q / (8 * M₃ : ℝ)) * |(p.1 : ℝ)| := by
    rw [div_lt_iff₀ hmabs] at hdiv
    exact hdiv
  have hmupper := abs_gmAffineSignedShell_le_scale hm₁
  calc
    |xi + ((p.1 * p.2 : ℤ) : ℝ)| =
        |xi + (p.1 : ℝ) * (p.2 : ℝ)| := by push_cast; rfl
    _ < (Q / (8 * M₃ : ℝ)) * |(p.1 : ℝ)| := hmul
    _ ≤ (Q / (8 * M₃ : ℝ)) * (2 * M₁ : ℝ) := by
      gcongr
    _ = testRadius M₁ M₃ Q := by
      unfold testRadius
      ring

example {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q)
    (hxi : testRadius M₁ M₃ Q ≤ |xi|) {p : ℤ × ℤ}
    (hp : p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi) :
    p.1 * p.2 ≠ 0 := by
  intro hz
  have hdev := show |xi + ((p.1 * p.2 : ℤ) : ℝ)| <
      testRadius M₁ M₃ Q from by
    exact (show |xi + ((p.1 * p.2 : ℤ) : ℝ)| <
      testRadius M₁ M₃ Q from by
        obtain ⟨hm₁, hell⟩ := mem_gmAffineFirstPoissonPairs.mp hp
        have hm₁neZ : p.1 ≠ 0 := gmAffineSignedShell_ne_zero hM₁ hm₁
        have hm₁neR : (p.1 : ℝ) ≠ 0 := by exact_mod_cast hm₁neZ
        have hnear : |(8 * M₃ : ℝ) *
            (xi / (p.1 : ℝ) + (p.2 : ℝ))| < Q := by
          unfold gmAffinePoissonNearSet at hell
          exact (Finset.mem_filter.mp hell).2
        have hrewrite : xi / (p.1 : ℝ) + (p.2 : ℝ) =
            (xi + (p.1 : ℝ) * (p.2 : ℝ)) / (p.1 : ℝ) := by
          field_simp [hm₁neR]
        rw [hrewrite, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 8 * M₃), abs_div] at hnear
        have hmabs : 0 < |(p.1 : ℝ)| := abs_pos.mpr hm₁neR
        have hscale : (0 : ℝ) < 8 * M₃ := by positivity
        have hdiv : |xi + (p.1 : ℝ) * (p.2 : ℝ)| / |(p.1 : ℝ)| <
            Q / (8 * M₃ : ℝ) := by
          rw [lt_div_iff₀ hscale]
          simpa only [mul_comm] using hnear
        have hmul : |xi + (p.1 : ℝ) * (p.2 : ℝ)| <
            (Q / (8 * M₃ : ℝ)) * |(p.1 : ℝ)| := by
          rw [div_lt_iff₀ hmabs] at hdiv
          exact hdiv
        calc
          |xi + ((p.1 * p.2 : ℤ) : ℝ)| =
              |xi + (p.1 : ℝ) * (p.2 : ℝ)| := by push_cast; rfl
          _ < (Q / (8 * M₃ : ℝ)) * |(p.1 : ℝ)| := hmul
          _ ≤ (Q / (8 * M₃ : ℝ)) * (2 * M₁ : ℝ) := by
            gcongr
            exact abs_gmAffineSignedShell_le_scale hm₁
          _ = testRadius M₁ M₃ Q := by
            unfold testRadius
            ring)
  rw [hz, Int.cast_zero, add_zero] at hdev
  exact (not_lt_of_ge hxi) hdev

noncomputable def testRange (M₁ M₃ : ℕ) (Q xi : ℝ) : Finset ℤ :=
  Finset.Icc ⌊-xi - testRadius M₁ M₃ Q⌋
    ⌈-xi + testRadius M₁ M₃ Q⌉

example {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q) :
    gmAffineFirstPoissonProducts M₁ M₃ Q xi ⊆
      testRange M₁ M₃ Q xi := by
  intro s hs
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
  have hdev := show |xi + ((p.1 * p.2 : ℤ) : ℝ)| <
      testRadius M₁ M₃ Q from by
    exact (by
      obtain ⟨hm₁, hell⟩ := mem_gmAffineFirstPoissonPairs.mp hp
      have hm₁neZ : p.1 ≠ 0 := gmAffineSignedShell_ne_zero hM₁ hm₁
      have hm₁neR : (p.1 : ℝ) ≠ 0 := by exact_mod_cast hm₁neZ
      have hnear : |(8 * M₃ : ℝ) *
          (xi / (p.1 : ℝ) + (p.2 : ℝ))| < Q := by
        unfold gmAffinePoissonNearSet at hell
        exact (Finset.mem_filter.mp hell).2
      have hrewrite : xi / (p.1 : ℝ) + (p.2 : ℝ) =
          (xi + (p.1 : ℝ) * (p.2 : ℝ)) / (p.1 : ℝ) := by
        field_simp [hm₁neR]
      rw [hrewrite, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 8 * M₃), abs_div] at hnear
      have hmabs : 0 < |(p.1 : ℝ)| := abs_pos.mpr hm₁neR
      have hscale : (0 : ℝ) < 8 * M₃ := by positivity
      have hdiv : |xi + (p.1 : ℝ) * (p.2 : ℝ)| / |(p.1 : ℝ)| <
          Q / (8 * M₃ : ℝ) := by
        rw [lt_div_iff₀ hscale]
        simpa only [mul_comm] using hnear
      have hmul : |xi + (p.1 : ℝ) * (p.2 : ℝ)| <
          (Q / (8 * M₃ : ℝ)) * |(p.1 : ℝ)| := by
        rw [div_lt_iff₀ hmabs] at hdiv
        exact hdiv
      calc
        |xi + ((p.1 * p.2 : ℤ) : ℝ)| =
            |xi + (p.1 : ℝ) * (p.2 : ℝ)| := by push_cast; rfl
        _ < (Q / (8 * M₃ : ℝ)) * |(p.1 : ℝ)| := hmul
        _ ≤ (Q / (8 * M₃ : ℝ)) * (2 * M₁ : ℝ) := by
          gcongr
          exact abs_gmAffineSignedShell_le_scale hm₁
        _ = testRadius M₁ M₃ Q := by
          unfold testRadius
          ring)
  rw [abs_lt] at hdev
  rw [testRange, Finset.mem_Icc]
  constructor
  · have hfloor := Int.floor_mono (show -xi - testRadius M₁ M₃ Q ≤
        ((p.1 * p.2 : ℤ) : ℝ) by linarith [hdev.1])
    rw [Int.floor_intCast] at hfloor
    simpa using hfloor
  · have hceil := Int.ceil_mono (show ((p.1 * p.2 : ℤ) : ℝ) ≤
        -xi + testRadius M₁ M₃ Q by linarith [hdev.2])
    rw [Int.ceil_intCast] at hceil
    simpa using hceil

example {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q) :
    ((gmAffineFirstPoissonProductRange M₁ M₃ Q xi).card : ℝ) ≤
      2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3 := by
  let R := gmAffineFirstPoissonRadius M₁ M₃ Q
  let a : ℤ := ⌊-xi - R⌋
  let b : ℤ := ⌈-xi + R⌉
  have hR : 0 ≤ R := by
    unfold R gmAffineFirstPoissonRadius
    positivity
  have haReal : (a : ℝ) ≤ -xi - R := by
    exact Int.floor_le (-xi - R)
  have hbReal : -xi + R ≤ (b : ℝ) := by
    exact Int.le_ceil (-xi + R)
  have habReal : (a : ℝ) ≤ (b : ℝ) := by linarith
  have hab : a ≤ b := by exact_mod_cast habReal
  have hdiff : 0 ≤ b + 1 - a := by omega
  have htoNat : (((b + 1 - a).toNat : ℕ) : ℤ) = b + 1 - a :=
    Int.toNat_of_nonneg hdiff
  have hcast : (((b + 1 - a).toNat : ℕ) : ℝ) =
      (b : ℝ) + 1 - (a : ℝ) := by
    exact_mod_cast htoNat
  have haClose := Int.lt_floor_add_one (-xi - R)
  have hbClose := Int.ceil_lt_add_one (-xi + R)
  rw [gmAffineFirstPoissonProductRange, Int.card_Icc]
  change (((b + 1 - a).toNat : ℕ) : ℝ) ≤ _
  rw [hcast]
  dsimp only [R] at haClose hbClose ⊢
  linarith

example {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi B : ℝ} (hQ : 0 < Q)
    (hxi : gmAffineFirstPoissonRadius M₁ M₃ Q ≤ |xi|)
    (hB : 0 ≤ B)
    (hprod : ∀ s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
      (s.natAbs : ℝ) ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
        C * B ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) := by
  obtain ⟨C, hC, hdiv⟩ := divisorCountBound_native epsilon hepsilon
  refine ⟨2 * C, by positivity, ?_⟩
  have hnonzero : ∀ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
      p.1 * p.2 ≠ 0 := by
    intro p hp
    exact gmAffineFirstPoissonPair_product_ne_zero hM₁ hM₃ hQ hxi hp
  have hnat := card_gmAffineFirstPoissonPairs_le_sum_divisors
    M₁ M₃ Q xi hnonzero
  have hreal : ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
      ∑ s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
        2 * (s.natAbs.divisors.card : ℝ) := by
    exact_mod_cast hnat
  calc
    ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
        ∑ s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
          2 * (s.natAbs.divisors.card : ℝ) := hreal
    _ ≤ ∑ _s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
          2 * (C * B ^ epsilon) := by
      apply Finset.sum_le_sum
      intro s hs
      have hs0 : s ≠ 0 := by
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
        exact hnonzero p hp
      have hdivs := hdiv s.natAbs (Int.natAbs_pos.mpr hs0)
      have hpow : (s.natAbs : ℝ) ^ epsilon ≤ B ^ epsilon :=
        Real.rpow_le_rpow (by positivity)
          (hprod s hs) hepsilon.le
      nlinarith [mul_le_mul_of_nonneg_left hpow hC.le]
    _ = (2 * C * B ^ epsilon) *
          ((gmAffineFirstPoissonProducts M₁ M₃ Q xi).card : ℝ) := by
      simp
      ring
    _ ≤ (2 * C) * B ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) := by
      have hcard := card_gmAffineFirstPoissonProducts_real_le
        hM₁ hM₃ (xi := xi) hQ
      have hcoef : 0 ≤ 2 * C * B ^ epsilon := by positivity
      nlinarith

example (M₁ M₃ : ℕ) (Q xi : ℝ) :
    (gmAffineFirstPoissonPairs M₁ M₃ Q xi).card =
      ∑ m₁ ∈ gmAffineSignedShell M₁,
        (gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q).card := by
  classical
  have hdis : Set.PairwiseDisjoint (↑(gmAffineSignedShell M₁))
      (fun m₁ : ℤ =>
        (gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q).image
          fun ell => (m₁, ell)) := by
    intro a ha b hb hab
    change Disjoint
      ((gmAffinePoissonNearSet M₃ (xi / (a : ℝ)) Q).image fun ell => (a, ell))
      ((gmAffinePoissonNearSet M₃ (xi / (b : ℝ)) Q).image fun ell => (b, ell))
    rw [Finset.disjoint_left]
    intro p hpa hpb
    obtain ⟨ella, hella, hpaEq⟩ := Finset.mem_image.mp hpa
    obtain ⟨ellb, hellb, hpbEq⟩ := Finset.mem_image.mp hpb
    apply hab
    have hfirst : (a, ella).1 = (b, ellb).1 := by rw [hpaEq, hpbEq]
    simpa using hfirst
  unfold gmAffineFirstPoissonPairs
  rw [Finset.card_biUnion hdis]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  rw [Finset.card_image_iff.mpr]
  intro a ha b hb hab
  exact congrArg Prod.snd hab

example {A : Type*} [AddCommMonoid A]
    (M₁ M₃ : ℕ) (Q xi : ℝ) (F : ℤ × ℤ → A) :
    ∑ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi, F p =
      ∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ ell ∈ gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q,
          F (m₁, ell) := by
  classical
  have hdis : Set.PairwiseDisjoint (↑(gmAffineSignedShell M₁))
      (fun m₁ : ℤ =>
        (gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q).image
          fun ell => (m₁, ell)) := by
    intro a ha b hb hab
    change Disjoint
      ((gmAffinePoissonNearSet M₃ (xi / (a : ℝ)) Q).image
        fun ell => (a, ell))
      ((gmAffinePoissonNearSet M₃ (xi / (b : ℝ)) Q).image
        fun ell => (b, ell))
    rw [Finset.disjoint_left]
    intro p hpa hpb
    obtain ⟨ella, hella, hpaEq⟩ := Finset.mem_image.mp hpa
    obtain ⟨ellb, hellb, hpbEq⟩ := Finset.mem_image.mp hpb
    apply hab
    have hfirst : (a, ella).1 = (b, ellb).1 := by rw [hpaEq, hpbEq]
    simpa using hfirst
  unfold gmAffineFirstPoissonPairs
  rw [Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact congrArg Prod.snd hab

noncomputable def testM2FourierBlock
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ : ℕ) (m₁ : ℤ) (xi : ℝ) : ℂ :=
  ∑ m₂ ∈ gmAffinePositiveShell M₂,
    (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
      fourier (gmAffineComplexify f)
        (((m₂ : ℝ) / (m₁ : ℝ)) * xi))

noncomputable def testFirstPoissonPairTerm
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) (hM₃ : 0 < M₃)
    (xi : ℝ) (p : ℤ × ℤ) : ℂ :=
  testM2FourierBlock f M₁ M₂ p.1 xi *
    gmAffineCentralPoissonKernel M₃ hM₃
      (xi / (p.1 : ℝ) + p.2)

example
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) (hM₃ : 0 < M₃)
    (Q xi : ℝ) :
    gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi =
      ∑ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
        testFirstPoissonPairTerm f M₁ M₂ M₃ hM₃ xi p := by
  rw [sum_gmAffineFirstPoissonPairs]
  unfold gmAffinePoissonMainFourier testFirstPoissonPairTerm
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  unfold testM2FourierBlock
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

example {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) :
    ((‖∑ i ∈ s, a i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, star (a i) * a j := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

example (f : SchwartzMap ℝ ℝ) (xi : ℝ) :
    fourier (gmAffineComplexify f) xi =
      ∫ u : ℝ, Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I) *
        (f u : ℂ) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with u
  rw [gmAffineComplexify_apply]
  simp only [Real.inner_apply, smul_eq_mul]
  congr 2
  push_cast
  ring

example (f : SchwartzMap ℝ ℝ) (xi : ℝ) :
    (starRingEnd ℂ) (fourier (gmAffineComplexify f) xi) =
      ∫ u : ℝ, Complex.exp ((((2 * Real.pi * u * xi) : ℝ) : ℂ) * I) *
        (f u : ℂ) := by
  rw [fourier_gmAffineComplexify_eq_integral]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with u
  have hexp :
      (starRingEnd ℂ) (Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I)) =
        Complex.exp ((((2 * Real.pi * u * xi) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, conj_ofReal, conj_I]
    push_cast
    ring
  rw [map_mul, hexp]
  simp

example (f : SchwartzMap ℝ ℝ) (m₂ m₂' : ℤ) (xi xi' : ℝ) :
    (starRingEnd ℂ) ((m₂' : ℂ) * fourier (gmAffineComplexify f) xi') *
        ((m₂ : ℂ) * fourier (gmAffineComplexify f) xi) =
      ∫ u' : ℝ, ∫ u : ℝ,
        (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
          Complex.exp ((((2 * Real.pi * (u' * xi' - u * xi)) : ℝ) : ℂ) * I) := by
  rw [map_mul, conj_fourier_gmAffineComplexify_eq_integral,
    fourier_gmAffineComplexify_eq_integral]
  simp only [map_intCast]
  let A : ℝ → ℂ := fun u' =>
    Complex.exp ((((2 * Real.pi * u' * xi') : ℝ) : ℂ) * I) * (f u' : ℂ)
  let B : ℝ → ℂ := fun u =>
    Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I) * (f u : ℂ)
  change ((m₂' : ℂ) * ∫ u', A u') * ((m₂ : ℂ) * ∫ u, B u) = _
  calc
    ((m₂' : ℂ) * ∫ u', A u') * ((m₂ : ℂ) * ∫ u, B u) =
        (∫ u', A u') * (((m₂' * m₂ : ℤ) : ℂ) * ∫ u, B u) := by
      push_cast
      ring
    _ = ∫ u' : ℝ, A u' * (((m₂' * m₂ : ℤ) : ℂ) * ∫ u, B u) := by
      rw [integral_mul_const]
    _ = ∫ u' : ℝ, ∫ u : ℝ, A u' * (((m₂' * m₂ : ℤ) : ℂ) * B u) := by
      apply integral_congr_ae
      filter_upwards with u'
      rw [integral_const_mul]
      rw [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u'
      apply integral_congr_ae
      filter_upwards with u
      dsimp only [A, B]
      calc
        Complex.exp ((((2 * Real.pi * u' * xi') : ℝ) : ℂ) * I) * (f u' : ℂ) *
            (((m₂' * m₂ : ℤ) : ℂ) *
              (Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I) * (f u : ℂ))) =
            (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
              (Complex.exp ((((2 * Real.pi * u' * xi') : ℝ) : ℂ) * I) *
                Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I)) := by ring
        _ = _ := by
          rw [← Complex.exp_add]
          congr 2
          push_cast
          ring

end RiemannZeta.GuthMaynard

namespace RiemannZeta.GuthMaynard

example (n : ℕ) (f : SchwartzMap ℝ ℝ) {A Q : ℝ}
    (hA : 0 < A) (hQ : 0 < Q)
    {M₂ : ℕ} (hM₂ : 0 < M₂) {ell : ℤ} {tau : ℝ}
    (htau : |tau| ≤ Q) (hell : 2 * Q / A ≤ |(ell : ℝ)|) :
    ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ≤
      ((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) *
        (SchwartzMap.seminorm ℝ n 0 (fourier (gmAffineComplexify f)) /
          ((M₂ : ℝ) * |(ell : ℝ)| / 2) ^ n) := by
  let B : ℝ := (M₂ : ℝ) * |(ell : ℝ)| / 2
  have hellpos : 0 < |(ell : ℝ)| := by
    have hleft : 0 < 2 * Q / A := by positivity
    exact hleft.trans_le hell
  have hBpos : 0 < B := by
    dsimp only [B]
    positivity
  apply norm_gmAffineMiddleFourierBlockReal_le_of_fourier_le
    f hA hM₂ htau hell (B := B)
  · exact le_rfl
  · intro x hx
    have hdecay := SchwartzMap.le_seminorm' ℝ n 0
      (fourier (gmAffineComplexify f)) x
    rw [iteratedDeriv_zero] at hdecay
    rw [le_div_iff₀ (pow_pos hBpos n)]
    have hp : B ^ n ≤ |x| ^ n := by gcongr
    simpa only [mul_comm] using
      ((mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans hdecay)

end RiemannZeta.GuthMaynard

namespace RiemannZeta.GuthMaynard

example (f : SchwartzMap ℝ ℝ) {A Q B F : ℝ}
    (hA : 0 < A) (hF : 0 ≤ F)
    {M₂ : ℕ} (hM₂ : 0 < M₂) {ell : ℤ} {tau : ℝ}
    (htau : |tau| ≤ Q) (hell : 2 * Q / A ≤ |(ell : ℝ)|)
    (hB : B ≤ (M₂ : ℝ) * |(ell : ℝ)| / 2)
    (hfourier : ∀ x : ℝ, B ≤ |x| →
      ‖fourier (gmAffineComplexify f) x‖ ≤ F) :
    ‖gmAffineMiddleFourierBlockReal f A M₂ ell tau‖ ≤
      ((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) * F := by
  unfold gmAffineMiddleFourierBlockReal
  calc
    ‖∑ m₂ ∈ gmAffinePositiveShell M₂,
        (m₂ : ℂ) * fourier (gmAffineComplexify f)
          ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / A) * tau)‖ ≤
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          ‖(m₂ : ℂ) * fourier (gmAffineComplexify f)
            ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / A) * tau)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m₂ ∈ gmAffinePositiveShell M₂, (2 * M₂ : ℝ) * F := by
      apply Finset.sum_le_sum
      intro m₂ hm₂
      rw [norm_mul, norm_intCast]
      have harg := gmAffineMiddleFourierArgument_abs_lower
        hA hm₂ htau hell
      have hfour := hfourier _ (hB.trans harg)
      exact mul_le_mul (abs_gmAffinePositiveShell_le_scale hm₂) hfour
        (norm_nonneg _) (by positivity)
    _ = ((gmAffinePositiveShell M₂).card : ℝ) * (2 * M₂ : ℝ) * F := by
      simp
      ring

end RiemannZeta.GuthMaynard

namespace RiemannZeta.GuthMaynard

example {A Q : ℝ} (hA : 0 < A) (hQ : 0 ≤ Q)
    {M₂ : ℕ} (hM₂ : 0 < M₂) {m₂ ell : ℤ}
    (hm₂ : m₂ ∈ gmAffinePositiveShell M₂) {tau : ℝ}
    (htau : |tau| ≤ Q) (hell : 2 * Q / A ≤ |(ell : ℝ)|) :
    (M₂ : ℝ) * |(ell : ℝ)| / 2 ≤
      |(ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / A) * tau| := by
  have hM₂r : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  have hm₂lower : (M₂ : ℝ) ≤ |(m₂ : ℝ)| :=
    gmAffinePositiveShell_scale_le_abs hm₂
  have htauDiv : |tau / A| ≤ Q / A := by
    rw [abs_div, abs_of_pos hA]
    exact div_le_div_of_nonneg_right htau hA.le
  have hrewrite : 2 * Q / A = 2 * (Q / A) := by ring
  rw [hrewrite] at hell
  have hhalf : Q / A ≤ |(ell : ℝ)| / 2 := by linarith
  have hinner : |(ell : ℝ)| / 2 ≤ |(ell : ℝ) + tau / A| := by
    have htri : |(ell : ℝ)| ≤ |(ell : ℝ) + tau / A| + |tau / A| := by
      calc
        |(ell : ℝ)| = |((ell : ℝ) + tau / A) - tau / A| := by ring_nf
        _ ≤ _ := abs_sub _ _
    linarith
  calc
    (M₂ : ℝ) * |(ell : ℝ)| / 2 = (M₂ : ℝ) * (|(ell : ℝ)| / 2) := by ring
    _ ≤ |(m₂ : ℝ)| * |(ell : ℝ) + tau / A| := by gcongr
    _ = |(ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / A) * tau| := by
      rw [← abs_mul]
      congr 1
      field_simp [hA.ne']

end RiemannZeta.GuthMaynard

namespace RiemannZeta.GuthMaynard

example
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q Y : ℝ} (hQ : 0 < Q) :
    (∑ m₁ ∈ gmAffineSignedShell M₁,
      ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
        ∫ xi : ℝ, gmAffineRetainedFirstPoissonPairSquare
          f Q M₂ M₃ hM₃ (m₁, ell) xi) ≤
      (32 * M₃ : ℝ) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2 *
        ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
          ∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
            ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2 := by
  let A : ℝ := SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual ^ 2
  let I : ℤ → ℝ := fun ell =>
    ∫ tau : ℝ, gmAffineMiddleTauWeight Q tau *
      ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hI (ell : ℤ) : 0 ≤ I ell := by
    dsimp only [I]
    apply integral_nonneg
    intro tau
    exact mul_nonneg (gmAffineMiddleTauWeight_nonneg Q tau) (sq_nonneg _)
  have hcoef {m₁ : ℤ} (hm₁ : m₁ ∈ gmAffineSignedShell M₁) :
      (8 * M₃ : ℝ) / |(m₁ : ℝ)| ≤ (8 * M₃ : ℝ) / M₁ := by
    exact div_le_div_of_nonneg_left (by positivity) hM₁r
      (gmAffineSignedShell_scale_le_abs hm₁)
  calc
    (∑ m₁ ∈ gmAffineSignedShell M₁,
      ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
        ∫ xi : ℝ, gmAffineRetainedFirstPoissonPairSquare
          f Q M₂ M₃ hM₃ (m₁, ell) xi) ≤
        ∑ _m₁ ∈ gmAffineSignedShell M₁,
          ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
            ((8 * M₃ : ℝ) / M₁) * A * I ell := by
      apply Finset.sum_le_sum
      intro m₁ hm₁
      apply Finset.sum_le_sum
      intro ell hell
      refine (integral_gmAffineRetainedFirstPoissonPairSquare_le
        f hM₁ hM₂ hM₃ hm₁ hQ).trans ?_
      dsimp only [A, I]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hcoef hm₁) (by positivity)) (hI ell)
    _ = ((gmAffineSignedShell M₁).card : ℝ) *
          (((8 * M₃ : ℝ) / M₁) * A *
            ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y, I ell) := by
      simp_rw [← Finset.mul_sum]
      simp
      ring
    _ ≤ (32 * M₃ : ℝ) * A *
          ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y, I ell := by
      have hcardNat := card_gmAffineSignedShell_le M₁
      have hcard : ((gmAffineSignedShell M₁).card : ℝ) ≤ 4 * M₁ := by
        exact_mod_cast (hcardNat.trans (by omega : 2 * (M₁ + 1) ≤ 4 * M₁))
      have hsum : 0 ≤ ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y, I ell := by
        apply Finset.sum_nonneg
        intro ell hell
        exact hI ell
      have hA : 0 ≤ A := by positivity
      calc
        ((gmAffineSignedShell M₁).card : ℝ) *
            (((8 * M₃ : ℝ) / M₁) * A *
              ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y, I ell) ≤
            (4 * M₁ : ℝ) * (((8 * M₃ : ℝ) / M₁) * A *
              ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y, I ell) := by
          gcongr
        _ = (32 * M₃ : ℝ) * A *
              ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y, I ell := by
          field_simp [hM₁r.ne']
          ring
    _ = _ := by rfl

end RiemannZeta.GuthMaynard

namespace RiemannZeta.GuthMaynard

example
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q Y D : ℝ} (hY : 0 ≤ Y) (hD : 0 ≤ D)
    (hcard : ∀ xi : ℝ,
      gmAffineFirstPoissonRadius M₁ M₃ Q < |xi| → |xi| ≤ Y →
      ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤ D) :
    (∫ xi in gmAffineMiddleFrequencyRegion
        (gmAffineFirstPoissonRadius M₁ M₃ Q) Y,
      ‖gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi‖ ^ 2) ≤
      D * ∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
          ∫ xi : ℝ, gmAffineRetainedFirstPoissonPairSquare
            f Q M₂ M₃ hM₃ (m₁, ell) xi := by
  let S : ℝ → ℝ := fun xi =>
    ∑ m₁ ∈ gmAffineSignedShell M₁,
      ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
        gmAffineRetainedFirstPoissonPairSquare
          f Q M₂ M₃ hM₃ (m₁, ell) xi
  have hterm (m₁ : ℤ) (hm₁ : m₁ ∈ gmAffineSignedShell M₁)
      (ell : ℤ) (hell : ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y) :
      Integrable (gmAffineRetainedFirstPoissonPairSquare
        f Q M₂ M₃ hM₃ (m₁, ell)) :=
    integrable_gmAffineRetainedFirstPoissonPairSquare
      f hM₁ hM₂ hM₃ hm₁ Q
  have hSint : Integrable S := by
    dsimp only [S]
    apply integrable_finsetSum
    intro m₁ hm₁
    apply integrable_finsetSum
    intro ell hell
    exact hterm m₁ hm₁ ell hell
  have hDSint : Integrable (fun xi => D * S xi) := hSint.const_mul D
  have hSnonneg (xi : ℝ) : 0 ≤ S xi := by
    dsimp only [S]
    apply Finset.sum_nonneg
    intro m₁ hm₁
    apply Finset.sum_nonneg
    intro ell hell
    unfold gmAffineRetainedFirstPoissonPairSquare
    split_ifs <;> positivity
  calc
    (∫ xi in gmAffineMiddleFrequencyRegion
        (gmAffineFirstPoissonRadius M₁ M₃ Q) Y,
      ‖gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi‖ ^ 2) ≤
        ∫ xi in gmAffineMiddleFrequencyRegion
          (gmAffineFirstPoissonRadius M₁ M₃ Q) Y, D * S xi := by
      apply integral_mono_of_nonneg
      · filter_upwards with xi
        exact sq_nonneg _
      · exact hDSint.integrableOn
      · filter_upwards [self_mem_ae_restrict
          (measurableSet_gmAffineMiddleFrequencyRegion
            (gmAffineFirstPoissonRadius M₁ M₃ Q) Y)] with xi hxi
        have hxi' := hxi
        rw [gmAffineMiddleFrequencyRegion] at hxi'
        have hmain := norm_gmAffinePoissonMainFourier_sq_le_pairs
          f M₁ M₂ M₃ hM₃ Q xi
        have hsum := sum_gmAffineFirstPoissonPairTerm_sq_eq_sum_retained_range
          (M₂ := M₂) (Q := Q) f hM₁ hM₃ hY hxi'.2
        rw [hsum] at hmain
        change _ ≤ D * S xi
        exact hmain.trans (mul_le_mul (hcard xi hxi'.1 hxi'.2) le_rfl
          (hSnonneg xi) (by positivity))
    _ ≤ ∫ xi : ℝ, D * S xi :=
      setIntegral_le_integral hDSint
        (Eventually.of_forall fun xi => mul_nonneg hD (hSnonneg xi))
    _ = D * ∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ ell ∈ gmAffineFirstPoissonEllRange M₁ M₃ Q Y,
          ∫ xi : ℝ, gmAffineRetainedFirstPoissonPairSquare
            f Q M₂ M₃ hM₃ (m₁, ell) xi := by
      rw [integral_const_mul]
      dsimp only [S]
      rw [MeasureTheory.integral_finsetSum (gmAffineSignedShell M₁) (by
        intro m₁ hm₁
        apply integrable_finsetSum
        intro ell hell
        exact hterm m₁ hm₁ ell hell)]
      apply congrArg (fun z : ℝ => D * z)
      apply Finset.sum_congr rfl
      intro m₁ hm₁
      rw [MeasureTheory.integral_finsetSum
        (gmAffineFirstPoissonEllRange M₁ M₃ Q Y) (hterm m₁ hm₁)]

end RiemannZeta.GuthMaynard

namespace RiemannZeta.GuthMaynard

example
    (f : SchwartzMap ℝ ℝ) {Q : ℝ} (hQ : 0 < Q)
    (M₂ M₃ : ℕ) (ell : ℤ) :
    Integrable (gmAffineRetainedMiddleProfile f Q M₂ M₃ ell) := by
  let H : ℝ → ℝ := fun tau =>
    ‖gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau‖ ^ 2 *
      ‖gmAffineLocalBumpDual tau‖ ^ 2
  have hblock : Continuous (fun tau : ℝ =>
      gmAffineMiddleFourierBlock f (8 * M₃) M₂ (-ell) tau) := by
    unfold gmAffineMiddleFourierBlock
    apply continuous_finset_sum
    intro m₂ hm₂
    exact continuous_const.mul
      ((fourier (gmAffineComplexify f)).continuous.comp (by fun_prop))
  have hHcont : Continuous H := by
    dsimp only [H]
    exact (continuous_norm.comp hblock).pow 2 |>.mul
      ((continuous_norm.comp gmAffineLocalBumpDual.continuous).pow 2)
  have hlocal : IntegrableOn H (Set.Ioo (-Q) Q) :=
    (hHcont.continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hind : Integrable (Set.indicator (Set.Ioo (-Q) Q) H) :=
    (integrable_indicator_iff measurableSet_Ioo).2 hlocal
  apply hind.congr
  filter_upwards with tau
  unfold gmAffineRetainedMiddleProfile
  by_cases htau : |tau| < Q
  · rw [if_pos htau, Set.indicator_of_mem]
    exact abs_lt.mp htau
  · rw [if_neg htau, Set.indicator_of_notMem]
    intro hmem
    exact htau (abs_lt.mpr hmem)

end RiemannZeta.GuthMaynard

namespace RiemannZeta.GuthMaynard

noncomputable def testEllRadius
    (M₁ M₃ : ℕ) (Q Y : ℝ) : ℝ :=
  Y / M₁ + Q / (8 * M₃ : ℝ)

noncomputable def testEllRange
    (M₁ M₃ : ℕ) (Q Y : ℝ) : Finset ℤ :=
  Finset.Icc (-⌈testEllRadius M₁ M₃ Q Y⌉)
    ⌈testEllRadius M₁ M₃ Q Y⌉

example {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q Y xi : ℝ} (hQ : 0 < Q) (hY : 0 ≤ Y) (hxi : |xi| ≤ Y)
    {p : ℤ × ℤ} (hp : p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi) :
    p.2 ∈ testEllRange M₁ M₃ Q Y := by
  have htau : |gmAffineFirstPoissonTau M₃ p.1 p.2 xi| < Q :=
    (mem_gmAffinePoissonNearSet_iff_firstPoissonTau hM₃).mp
      (mem_gmAffineFirstPoissonPairs.mp hp).2
  have hp₁ := (mem_gmAffineFirstPoissonPairs.mp hp).1
  have hp₁ne : (p.1 : ℝ) ≠ 0 := by
    exact_mod_cast gmAffineSignedShell_ne_zero hM₁ hp₁
  have hp₁lower : (M₁ : ℝ) ≤ |(p.1 : ℝ)| :=
    gmAffineSignedShell_scale_le_abs hp₁
  have hA : (0 : ℝ) < 8 * M₃ := by positivity
  have hnear : |xi / (p.1 : ℝ) + (p.2 : ℝ)| < Q / (8 * M₃ : ℝ) := by
    unfold gmAffineFirstPoissonTau at htau
    rw [abs_mul, abs_of_pos hA] at htau
    apply (lt_div_iff₀ hA).2
    simpa [mul_comm] using htau
  have hxiDiv : |xi / (p.1 : ℝ)| ≤ Y / M₁ := by
    rw [abs_div]
    calc
      |xi| / |(p.1 : ℝ)| ≤ Y / |(p.1 : ℝ)| :=
        (div_le_div_iff_of_pos_right (abs_pos.mpr hp₁ne)).2 hxi
      _ ≤ Y / M₁ :=
        div_le_div_of_nonneg_left hY (by positivity) hp₁lower
  have hellBound : |(p.2 : ℝ)| < testEllRadius M₁ M₃ Q Y := by
    have htri : |(p.2 : ℝ)| ≤
        |xi / (p.1 : ℝ) + (p.2 : ℝ)| + |xi / (p.1 : ℝ)| := by
      calc
        |(p.2 : ℝ)| =
            |(xi / (p.1 : ℝ) + (p.2 : ℝ)) - xi / (p.1 : ℝ)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    unfold testEllRadius
    linarith
  have hceil : |(p.2 : ℝ)| ≤
      (⌈testEllRadius M₁ M₃ Q Y⌉ : ℝ) :=
    hellBound.le.trans (Int.le_ceil _)
  rw [testEllRange, Finset.mem_Icc]
  constructor
  · have hreal : (-(⌈testEllRadius M₁ M₃ Q Y⌉ : ℤ) : ℝ) ≤ (p.2 : ℝ) := by
      exact (neg_le_neg hceil).trans (neg_abs_le (p.2 : ℝ))
    exact_mod_cast hreal
  · have hreal : (p.2 : ℝ) ≤ (⌈testEllRadius M₁ M₃ Q Y⌉ : ℝ) :=
      (le_abs_self (p.2 : ℝ)).trans hceil
    exact_mod_cast hreal

end RiemannZeta.GuthMaynard
#check MeasureTheory.integral_mono_ae
#check MeasureTheory.integral_mono_of_nonneg
#check MeasureTheory.integral_mono
#check MeasureTheory.integral_add
#check norm_integral_le_integral_norm
#check Finset.sum_bij
#check Finset.sum_bij'
#check Finset.sum_le_sum_of_subset_of_nonneg

namespace RiemannZeta.GuthMaynard

example
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ} (hM₃ : 0 < M₃)
    (Q xi : ℝ) :
    ∑ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
        ‖gmAffineFirstPoissonPairTerm f M₂ M₃ hM₃ xi p‖ ^ 2 =
      ∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑' ell : ℤ,
          gmAffineRetainedFirstPoissonPairSquare
            f Q M₂ M₃ hM₃ (m₁, ell) xi := by
  rw [sum_gmAffineFirstPoissonPairs]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  rw [tsum_eq_sum (s :=
    gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q)]
  · apply Finset.sum_congr rfl
    intro ell hell
    unfold gmAffineRetainedFirstPoissonPairSquare
    rw [if_pos ((mem_gmAffinePoissonNearSet_iff_firstPoissonTau hM₃).mp hell)]
  · intro ell hell
    unfold gmAffineRetainedFirstPoissonPairSquare
    rw [if_neg]
    intro htau
    exact hell ((mem_gmAffinePoissonNearSet_iff_firstPoissonTau hM₃).mpr htau)

end RiemannZeta.GuthMaynard
#check memLp_norm_rpow_iff
#check MemLp.restrict
#check Real.sqrt_eq_rpow
#check Real.sum_sqrt_mul_sqrt_le
#check Finset.sum_mul
#check Finset.mul_sum
#check MeasureTheory.integral_mono_measure

theorem probe_memLp_sqrt_four_of_memLp_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hmeas : AEStronglyMeasurable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (hf : MemLp f (2 : ENNReal) μ) :
    MemLp (fun x => Real.sqrt (f x)) (4 : ENNReal) μ := by
  have hpow := (memLp_norm_rpow_iff
    (p := (2 : ENNReal)) (q := (1 / 2 : ENNReal)) hmeas (by norm_num) (by norm_num)).2 hf
  have heq : (fun x => Real.sqrt (f x)) =
      (fun x => ‖f x‖ ^ (1 / 2 : ENNReal).toReal) := by
    funext x
    rw [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    norm_num
  rw [heq]
  convert hpow using 1
  rw [ENNReal.div_eq_inv_mul]
  norm_num

#check ContinuousOn.integrableOn_Icc
#check ContinuousOn.integrableOn_compact
#check Continuous.continuousOn
#check ContinuousOn.sqrt
#check MeasureTheory.MemLp.const_mul
#check MeasureTheory.MemLp.mul
#check Continuous.comp_continuousOn
#check ContinuousOn.comp
#check ContinuousOn.inv₀
#check MeasureTheory.integral_finset_sum
#check MeasureTheory.integral_finsetSum
