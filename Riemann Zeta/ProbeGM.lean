import RiemannZeta.GuthMaynard.LargeValuesAffineIteration

open Complex Finset Filter FourierTransform MeasureTheory Real Set
open scoped ComplexConjugate ContDiff FourierTransform Topology

namespace RiemannZeta.GuthMaynard


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
#check MeasureTheory.integral_mono_ae
#check MeasureTheory.integral_mono_of_nonneg
#check MeasureTheory.integral_mono
#check MeasureTheory.integral_add
#check norm_integral_le_integral_norm
