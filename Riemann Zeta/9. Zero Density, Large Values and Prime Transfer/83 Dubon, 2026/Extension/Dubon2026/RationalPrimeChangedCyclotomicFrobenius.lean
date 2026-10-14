import Dubon2026.RationalPrimeChangedCyclotomicUniformizer
import Dubon2026.LocalFieldArithmeticFrobeniusUniqueness
import Dubon2026.SurjectiveLocalResidue

/-! # The changed cyclotomic diagonal automorphism is arithmetic Frobenius

The diagonal automorphism reduces to the prime-power map on the explicit
Witt cyclotomic DVR.  The changed Eisenstein presentation shows that the
auxiliary local field has the original residue cardinality.  The ambient-DVR
valuation comparison then transports the residue action to the actual
changed/cyclotomic compositum, where unramified Frobenius uniqueness identifies
the restricted diagonal automorphism with positive arithmetic Frobenius.
This discharges the last Frobenius premise in DUB-17's norm-uniformizer
reciprocity step.
-/
namespace Dubon2026
noncomputable section
open Polynomial
open scoped ValuativeRel

set_option maxHeartbeats 800000

attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootDVR
  wittCyclotomicRootFinite

theorem wittCyclotomicDiagonalFrobenius_residue
    (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)])
    (x : wittCyclotomicRootAlgebra p n) :
    IsLocalRing.residue (wittCyclotomicRootAlgebra p n)
        (wittCyclotomicDiagonalFrobenius p n a b ha hb hab x) =
      IsLocalRing.residue (wittCyclotomicRootAlgebra p n) x ^ p := by
  let W := WittVector p (AlgebraicClosure (ZMod p))
  let B := wittCyclotomicRootAlgebra p n
  let σ := wittCyclotomicDiagonalFrobenius p n a b ha hb hab
  let r := IsLocalRing.residue B
  have hcomap : (IsLocalRing.maximalIdeal B).comap (algebraMap W B) =
      IsLocalRing.maximalIdeal W :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (R := W) (IsLocalRing.maximalIdeal B))
  letI : IsLocalHom (algebraMap W B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap W B)).out 4 0).mp hcomap
  letI : CharP (IsLocalRing.ResidueField B) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr <| by
      change r (p : B) = 0
      rw [IsLocalRing.residue_eq_zero_iff]
      change algebraMap W B (p : W) ∈ IsLocalRing.maximalIdeal B
      apply map_nonunit (algebraMap W B)
      rw [IsLocalRing.mem_maximalIdeal]
      exact (WittVector.irreducible p).not_isUnit
  have hhom : r.comp σ.toRingHom =
      (frobenius (IsLocalRing.ResidueField B) p).comp r := by
    apply AdjoinRoot.ringHom_ext
    · ext c
      simp only [RingHom.comp_apply]
      rw [show σ.toRingHom ((AdjoinRoot.of
          (primePowerShiftedCyclotomic W p n)) c) =
          algebraMap W B (WittVector.frobenius c) from
        wittCyclotomicDiagonalFrobenius_coefficient p n a b ha hb hab c]
      rw [frobenius_def]
      change r (algebraMap W B (WittVector.frobenius c)) =
        r (algebraMap W B c) ^ p
      rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      rw [← map_pow, ← map_sub]
      apply map_nonunit (algebraMap W B)
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer (p : W)).mp
        (WittVector.irreducible p)]
      rw [← WittVector.ker_constantCoeff]
      change WittVector.constantCoeff (WittVector.frobenius c - c ^ p) = 0
      simp only [map_sub, map_pow, WittVector.constantCoeff_apply,
        WittVector.coeff_frobenius_charP]
      exact sub_self _
    · simp only [RingHom.comp_apply]
      rw [show σ.toRingHom (AdjoinRoot.root
          (primePowerShiftedCyclotomic W p n)) =
          (wittCyclotomicPrimitiveRoot p n) ^ b - 1 from
        wittCyclotomicDiagonalFrobenius_root p n a b ha hb hab]
      rw [frobenius_def]
      change r ((1 + AdjoinRoot.root
          (primePowerShiftedCyclotomic W p n)) ^ b - 1) =
        r (AdjoinRoot.root (primePowerShiftedCyclotomic W p n)) ^ p
      have hroot : r (AdjoinRoot.root (primePowerShiftedCyclotomic W p n)) = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff, wittCyclotomicRoot_maximalIdeal]
        exact Ideal.subset_span (Set.mem_singleton _)
      rw [map_sub, map_pow, map_add, map_one, hroot]
      rw [zero_pow (Fact.out : p.Prime).ne_zero, add_zero, one_pow, sub_self]
  exact RingHom.congr_fun hhom x

attribute [local instance] rationalPrimeWittPrime
  wittCyclotomicRootDomain wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra
  wittCyclotomicFieldTower rationalPrimeWittOriginalAlgebra
  rationalPrimeWittCyclotomicAlgebra rationalPrimeWittCyclotomicTower
  rationalPrimeWittCyclotomicModule rationalPrimeWittCyclotomicMulAction
  rationalPrimeChangedIntegralRootDomain rationalPrimeChangedIntegralRootDVR

theorem rationalPrimeChangedAuxiliary_residue_card
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryField p hp n u)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryField p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryField p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u))] :
    Nat.card 𝓀[rationalPrimeChangedAuxiliaryField p hp n u] = p := by
  let K := rationalPrimeLocalField p hp
  let E := rationalPrimeChangedAuxiliaryField p hp n u
  let f := rationalPrimeChangedIntegralPolynomial p hp n u
  let A := AdjoinRoot f
  letI : Algebra A E :=
    (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha).toAlgebra
  haveI : IsScalarTower 𝒪[K] A E := IsScalarTower.of_algebraMap_eq fun x =>
    (rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha).commutes x |>.symm
  haveI : IsFractionRing A E :=
    rationalPrimeChangedAuxiliaryField_isFractionRing p hp n a u hu ha
  let e := localFieldMonicRootIntegerEquiv K E f
    (rationalPrimeChangedIntegralPolynomial_monic p hp n u)
  let θE : 𝒪[E] := e (AdjoinRoot.root f)
  have hθE : Irreducible θE :=
    (MulEquiv.irreducible_iff (f := e.toMulEquiv)).mpr
      (rationalPrimeChangedIntegralRoot_irreducible p hp n u)
  have hθres : IsLocalRing.residue 𝒪[E] θE = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    exact hθE.not_isUnit
  have hpoly :
      (IsLocalRing.residue 𝒪[E]).comp
          (e.toRingEquiv.toRingHom.comp (AdjoinRoot.mk f)) =
        Polynomial.eval₂RingHom
          ((IsLocalRing.residue 𝒪[E]).comp (algebraMap 𝒪[K] 𝒪[E])) 0 := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, AdjoinRoot.mk_C]
      change IsLocalRing.residue 𝒪[E]
          (e (algebraMap 𝒪[K] A c)) =
        IsLocalRing.residue 𝒪[E] (algebraMap 𝒪[K] 𝒪[E] c)
      rw [e.commutes]
    · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, AdjoinRoot.mk_X]
      exact hθres
  have hsur : Function.Surjective
      (IsLocalRing.ResidueField.map (algebraMap 𝒪[K] 𝒪[E])) := by
    intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    let x : A := e.symm z
    have hx : e x = z := e.apply_symm_apply z
    have hc : ∃ c : 𝒪[K], IsLocalRing.residue 𝒪[E] (e x) =
        IsLocalRing.residue 𝒪[E] (algebraMap 𝒪[K] 𝒪[E] c) := by
      refine AdjoinRoot.induction_on (f := f) x ?_
      intro P
      refine ⟨P.coeff 0, ?_⟩
      have hP := RingHom.congr_fun hpoly P
      simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_at_zero] using hP
    obtain ⟨c, hc⟩ := hc
    refine ⟨IsLocalRing.residue 𝒪[K] c, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue]
    simpa only [hx] using hc.symm
  let er : 𝓀[K] ≃+* 𝓀[E] := RingEquiv.ofBijective
    (IsLocalRing.ResidueField.map (algebraMap 𝒪[K] 𝒪[E]))
    ⟨(IsLocalRing.ResidueField.map (algebraMap 𝒪[K] 𝒪[E])).injective, hsur⟩
  calc
    Nat.card 𝓀[E] = Nat.card 𝓀[K] := (Nat.card_congr er.toEquiv).symm
    _ = p := rationalPrimeLocalField_residue_card p hp

theorem rationalPrimeChangedCyclotomicCompositum_valuationSubring_eq_ambient
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryField p hp n u)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryField p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryField p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u))]
    [ValuativeRel (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [TopologicalSpace (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicCompositum p hp n u))] :
    let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
    let M := rationalPrimeChangedCyclotomicCompositum p hp n u
    let B := wittCyclotomicRootAlgebra q n
    let Ω := wittCyclotomicField q n
    let ι : M →+* Ω := M.val.toRingHom
    (ValuativeRel.valuation M).valuationSubring =
      (((IsDiscreteValuationRing.maximalIdeal B).valuation Ω).comap ι).valuationSubring := by
  dsimp only
  let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
  let E := rationalPrimeChangedAuxiliaryField p hp n u
  let M := rationalPrimeChangedCyclotomicCompositum p hp n u
  let B := wittCyclotomicRootAlgebra q n
  let Ω := wittCyclotomicField q n
  let j : 𝒪[E] →+* B :=
    rationalPrimeChangedAuxiliaryIntegerAmbientMap p hp n a u hu ha
  let ι : M →+* Ω := M.val.toRingHom
  have hjfield : (algebraMap B Ω).comp j =
      E.val.toRingHom.comp (algebraMap 𝒪[E] E) :=
    rationalPrimeChangedAuxiliaryIntegerAmbientMap_field p hp n a u hu ha
  have hcomp : (algebraMap B Ω).comp j =
      ι.comp (algebraMap 𝒪[E] M) := by
    rw [hjfield]
    ext z
    rfl
  let vΩ := (IsDiscreteValuationRing.maximalIdeal B).valuation Ω
  let π : M := rationalPrimeChangedCyclotomicCompositumRoot p hp n u - 1
  let rootB : B := AdjoinRoot.root
    (primePowerShiftedCyclotomic (WittVector q (AlgebraicClosure (ZMod q))) q n)
  let rootInteger : vΩ.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring rootB
  have hrootInteger : Irreducible rootInteger :=
    (MulEquiv.irreducible_iff
      (f := (IsDiscreteValuationRing.equivValuationSubring
        (A := B) (K := Ω)).toMulEquiv)).mpr
      (wittCyclotomicRoot_irreducible q n)
  have hrootUniformizer : vΩ.IsUniformizer (algebraMap B Ω rootB) := by
    have h := vΩ.isUniformizer_of_maximalIdeal_eq_span
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer rootInteger).mp
        hrootInteger)
    exact h
  have hπ : vΩ.IsUniformizer (ι π) := by
    convert hrootUniformizer using 1
    change algebraMap B Ω (1 + rootB) - 1 = algebraMap B Ω rootB
    rw [map_add, map_one, add_sub_cancel_left]
  exact localField_integer_valuationSubring_eq_comap_of_integral_embedding
    E M B Ω j ι hcomp π hπ

theorem rationalPrimeChangedCyclotomicDiagonalAlgEquiv_residue
    (p : ℕ) (hp : p.Prime) (n a b : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (hcoprimeA : a.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hcoprimeB : b.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD
      (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)])
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryField p hp n u)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryField p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryField p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u))]
    [ValuativeRel (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [TopologicalSpace (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicCompositum p hp n u))] :
    let E := rationalPrimeChangedAuxiliaryField p hp n u
    let M := rationalPrimeChangedCyclotomicCompositum p hp n u
    ∀ x : 𝒪[M],
      IsLocalRing.residue 𝒪[M]
          (localFieldIntegerGaloisEquiv E M
            (rationalPrimeChangedCyclotomicDiagonalAlgEquiv
              p hp n a b u hu hcoprimeA hcoprimeB hab) x) =
        IsLocalRing.residue 𝒪[M] x ^ Nat.card 𝓀[E] := by
  dsimp only
  let q := Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)
  let E := rationalPrimeChangedAuxiliaryField p hp n u
  let M := rationalPrimeChangedCyclotomicCompositum p hp n u
  let B := wittCyclotomicRootAlgebra q n
  let Ω := wittCyclotomicField q n
  let ι : M →+* Ω := M.val.toRingHom
  let vM := ValuativeRel.valuation M
  let vΩ := (IsDiscreteValuationRing.maximalIdeal B).valuation Ω
  let σB := wittCyclotomicDiagonalFrobenius q n a b hcoprimeA hcoprimeB hab
  let σΩ := wittCyclotomicDiagonalFieldFrobenius q n a b hcoprimeA hcoprimeB hab
  let g := rationalPrimeChangedCyclotomicDiagonalAlgEquiv
    p hp n a b u hu hcoprimeA hcoprimeB hab
  intro x
  have hcard : Nat.card 𝓀[E] = p :=
    rationalPrimeChangedAuxiliary_residue_card p hp n a u hu ha
  suffices haction :
      IsLocalRing.residue 𝒪[M] (localFieldIntegerGaloisEquiv E M g x) =
        IsLocalRing.residue 𝒪[M] x ^ p by
    exact haction.trans (congrArg
      (fun e : ℕ => IsLocalRing.residue 𝒪[M] x ^ e) hcard.symm)
  have hsub : vM.valuationSubring = (vΩ.comap ι).valuationSubring :=
    rationalPrimeChangedCyclotomicCompositum_valuationSubring_eq_ambient
      p hp n a u hu ha
  have hEquiv : vM.IsEquiv (vΩ.comap ι) :=
    (Valuation.isEquiv_iff_valuationSubring vM (vΩ.comap ι)).mpr hsub
  have hxAmbient : vΩ (ι (x : M)) ≤ 1 := by
    have hxTarget : vM (x : M) ≤ vM 1 := by
      simpa only [map_one] using x.property
    have hxComap : (vΩ.comap ι) (x : M) ≤ (vΩ.comap ι) 1 :=
      (hEquiv.le_iff_le (x := (x : M)) (y := (1 : M))).1 hxTarget
    simpa only [Valuation.comap_apply, map_one] using hxComap
  let eB := IsDiscreteValuationRing.equivValuationSubring (A := B) (K := Ω)
  letI : IsLocalHom eB := isLocalHom_equiv eB
  letI : IsLocalHom eB.toRingHom := isLocalHom_toRingHom eB
  let xAmbient : vΩ.valuationSubring := ⟨ι (x : M), hxAmbient⟩
  let bx : B := eB.symm xAmbient
  have hbx : algebraMap B Ω bx = ι (x : M) := by
    have h := eB.apply_symm_apply xAmbient
    exact congrArg Subtype.val h
  have hres : IsLocalRing.residue B (σB bx) =
      IsLocalRing.residue B bx ^ q :=
    wittCyclotomicDiagonalFrobenius_residue
      q n a b hcoprimeA hcoprimeB hab bx
  have hBmax : σB bx - bx ^ q ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hres, sub_self]
  let diffB : B := σB bx - bx ^ q
  let diffInteger : vΩ.valuationSubring := eB diffB
  have hdiffIntegerMax : diffInteger ∈
      IsLocalRing.maximalIdeal vΩ.valuationSubring := by
    exact map_nonunit eB.toRingHom diffB hBmax
  have hdiffAmbient : vΩ (algebraMap B Ω diffB) < 1 := by
    have h := (Valuation.mem_maximalIdeal_iff (v := vΩ)).1 hdiffIntegerMax
    simpa only [diffInteger, eB] using h
  have hmapdiff : algebraMap B Ω diffB =
      ι (g (x : M) - (x : M) ^ q) := by
    calc
      algebraMap B Ω diffB =
          algebraMap B Ω (σB bx) - (algebraMap B Ω bx) ^ q := by
            simp only [diffB, map_sub, map_pow]
      _ = σΩ (algebraMap B Ω bx) - (algebraMap B Ω bx) ^ q := by
            rw [wittCyclotomicDiagonalFieldFrobenius_integer]
      _ = σΩ (ι (x : M)) - (ι (x : M)) ^ q := by rw [hbx]
      _ = ι (g (x : M)) - (ι (x : M)) ^ q := by rfl
      _ = ι (g (x : M) - (x : M) ^ q) := by
            rw [ι.map_sub, ι.map_pow]
  have htargetDiff : vM (g (x : M) - (x : M) ^ q) < 1 := by
    have hambient : vΩ (ι (g (x : M) - (x : M) ^ q)) < 1 := by
      rw [← hmapdiff]
      exact hdiffAmbient
    have hcomap : (vΩ.comap ι) (g (x : M) - (x : M) ^ q) <
        (vΩ.comap ι) 1 := by
      simpa only [Valuation.comap_apply, map_one] using hambient
    have htarget := (hEquiv.lt_iff_lt
      (x := g (x : M) - (x : M) ^ q) (y := (1 : M))).2 hcomap
    simpa only [map_one] using htarget
  let y : 𝒪[M] := localFieldIntegerGaloisEquiv E M g x - x ^ q
  have hyValuation : vM (y : M) < 1 := by
    let ιM : 𝒪[M] →+* M := algebraMap 𝒪[M] M
    have hAction : ιM (localFieldIntegerGaloisEquiv E M g x) = g (x : M) := by
      simpa only [ιM] using localFieldIntegerGaloisEquiv_apply E M g x
    have hyCoe : ιM (localFieldIntegerGaloisEquiv E M g x - x ^ q) =
        g (x : M) - (x : M) ^ q := by
      calc
        ιM (localFieldIntegerGaloisEquiv E M g x - x ^ q) =
            ιM (localFieldIntegerGaloisEquiv E M g x) - ιM (x ^ q) :=
          ιM.map_sub _ _
        _ = g (x : M) - (ιM x) ^ q := congrArg₂ (· - ·) hAction (ιM.map_pow x q)
        _ = g (x : M) - (x : M) ^ q := by rfl
    change vM (ιM (localFieldIntegerGaloisEquiv E M g x - x ^ q)) < 1
    exact hyCoe.symm ▸ htargetDiff
  have hyMaximal : y ∈ IsLocalRing.maximalIdeal 𝒪[M] :=
    (Valuation.mem_maximalIdeal_iff (v := vM)).2 hyValuation
  have hyResidue : IsLocalRing.residue 𝒪[M] y = 0 :=
    (IsLocalRing.residue_eq_zero_iff y).2 hyMaximal
  let rM := IsLocalRing.residue 𝒪[M]
  have hyResidue' :
      rM (localFieldIntegerGaloisEquiv E M g x - x ^ q) = 0 := by
    simpa only [rM, y] using hyResidue
  have hq :
      IsLocalRing.residue 𝒪[M] (localFieldIntegerGaloisEquiv E M g x) =
        IsLocalRing.residue 𝒪[M] x ^ q := by
    apply sub_eq_zero.mp
    simpa only [rM, rM.map_sub, rM.map_pow] using hyResidue'
  simpa only [q, rationalPrimePlace_natGenerator] using hq

/-- The restricted diagonal automorphism on the actual changed/cyclotomic
compositum is the positive arithmetic Frobenius.  The preceding theorem
supplies its residue action, and unramified Frobenius uniqueness supplies the
identification. -/
theorem rationalPrimeChangedCyclotomicDiagonalAlgEquiv_eq_arithmeticFrobenius
    (p : ℕ) (hp : p.Prime) (n a b : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    (hcoprimeA : a.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hcoprimeB : b.Coprime
      ((Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD
      (Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp)) ^ (n + 1)])
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryField p hp n u)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryField p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryField p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u))]
    [ValuativeRel (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [TopologicalSpace (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedCyclotomicCompositum p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedCyclotomicCompositum p hp n u))]
    [Algebra.FormallyUnramified
      𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
      𝒪[rationalPrimeChangedCyclotomicCompositum p hp n u]] :
    rationalPrimeChangedCyclotomicDiagonalAlgEquiv
        p hp n a b u hu hcoprimeA hcoprimeB hab =
      localFieldArithmeticFrobenius
        (rationalPrimeChangedAuxiliaryField p hp n u)
        (rationalPrimeChangedCyclotomicCompositum p hp n u) := by
  apply localFieldArithmeticFrobenius_eq_of_residue
  exact rationalPrimeChangedCyclotomicDiagonalAlgEquiv_residue
    p hp n a b u hu ha hcoprimeA hcoprimeB hab

end
end Dubon2026
