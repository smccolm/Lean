import TaoTrudgianYang2025.HuxleyLinearForms
import Mathlib.Tactic
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators ContDiff
namespace HuxleyTriangularRegimeScratch

private theorem two_thirds_cube {x : ℝ} (hx : 0 ≤ x) :
    (x^((2:ℝ)/3))^3=x^2 := by
  rw [←Real.rpow_natCast,←Real.rpow_mul hx]
  norm_num

/-- The single physical regime from (10.7) controls both cubic-root
and short-family translation terms; the logarithmic budget is explicit. -/
theorem triangular_translation_source_regime
    {M N R U L : ℝ} (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 ≤ U) (hL : 0 ≤ L) (hRN : R ≤ N)
    (hselected : U ≤ (N/R)^((2:ℝ)/3))
    (hregime : N^4 ≤ M*R^3*L^((3:ℝ)/2)) :
    N^2*U ≤ (M*R^2)^((2:ℝ)/3)*L ∧
      N^3*U ≤ M*R^2*L^((3:ℝ)/2) := by
  have hLpow : (L^((3:ℝ)/2))^2=L^3 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hL]
    norm_num
  have hN8 : N^8 ≤ M^2*R^6*L^3 := by
    calc
      _ = (N^4)^2 := by ring
      _ ≤ (M*R^3*L^((3:ℝ)/2))^2 := by gcongr
      _ = _ := by rw [mul_pow,mul_pow,hLpow]; ring
  have hUcube : U^3 ≤ (N/R)^2 := by
    calc
      _ ≤ ((N/R)^((2:ℝ)/3))^3 := by gcongr
      _ = _ := two_thirds_cube (div_nonneg hN.le hR.le)
  have hcube : (N^2*U)^3 ≤ ((M*R^2)^((2:ℝ)/3)*L)^3 := by
    calc
      _ = N^6*U^3 := by ring
      _ ≤ N^6*(N/R)^2 := mul_le_mul_of_nonneg_left hUcube (by positivity)
      _ = N^8/R^2 := by field_simp
      _ ≤ (M^2*R^6*L^3)/R^2 :=
        div_le_div_of_nonneg_right hN8 (sq_nonneg R)
      _ = _ := by rw [mul_pow,two_thirds_cube (by positivity : (0:ℝ) ≤ M*R^2)]; field_simp
  constructor
  · exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 3≠0)).mp hcube
  · have hratio : 1 ≤ N/R := (le_div_iff₀ hR).mpr (by simpa only [one_mul] using hRN)
    have hlinear : U ≤ N/R := hselected.trans
      ((Real.rpow_le_rpow_of_exponent_le hratio (by norm_num : (2:ℝ)/3 ≤ 1)).trans_eq (Real.rpow_one _))
    calc
      _ ≤ N^3*(N/R) := mul_le_mul_of_nonneg_left hlinear (by positivity)
      _ = N^4/R := by ring
      _ ≤ (M*R^3*L^((3:ℝ)/2))/R := div_le_div_of_nonneg_right hregime hR.le
      _ = _ := by field_simp

example
    {M N R U L : ℝ} (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 ≤ U) (hL : 0 ≤ L) (hRN : R ≤ N)
    (hselected : U ≤ (N/R)^((2:ℝ)/3))
    (hregime : N^4 ≤ M*R^3*L^((3:ℝ)/2)) :
    N^2*U ≤ (M*R^2)^((2:ℝ)/3)*L ∧
      N^3*U ≤ M*R^2*L^((3:ℝ)/2) :=
  HuxleyTriangularRegimeScratch.triangular_translation_source_regime (M:=M) (N:=N) (R:=R) (U:=U) (L:=L) hM hN hR hU hL hRN hselected hregime


/-- The model third derivative prevents the actual normalized source
amplitude from degenerating. No lower comparison between Tsrc and T
is assumed. -/
theorem positive_difference_approximate_model_source_amplitude
    (Fsrc : ℝ → ℝ) {σsrc Usrc η y Tsrc T σ δ : ℝ}
    (hσsrc : 0 < σsrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) :
    let F := fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y))/(σsrc*η)
    Expdb.IsApproximateModelPhaseFunction F σ 2 δ →
      modelPhaseThirdLower σ*σsrc*T/(3*Usrc) ≤ Tsrc := by
  intro F hF
  let G := fun u => (Fsrc u-Fsrc (u+η*y))/(σsrc*η)
  have hFu : F=fun u => (Tsrc/T)*G u := by
    funext u
    dsimp only [F,G]
    ring
  have hd : iteratedDeriv 3 F (3/2)=
      (Tsrc/T)*iteratedDeriv 3 G (3/2) := by
    rw [hFu,iteratedDeriv_const_mul_field]
  have hlow : modelPhaseThirdLower σ ≤ iteratedDeriv 3 F (3/2) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      (approximateModelPhase_thirdDeriv_bounds hσ hδ hF
        (by norm_num : (3/2:ℝ)∈Ioo (1:ℝ) 2)).1
  have hu := positive_jets_difference_mixed_upper Fsrc hσsrc hUsrc hη hηmax
    (by norm_num : (3/2:ℝ)∈Icc (3/4:ℝ) (9/4))
    (show y∈Icc (1/2:ℝ) 3 from
      ⟨by linarith only [hy.1],by linarith only [hy.2]⟩)
    hreg hjets 3 0 (by norm_num) (by norm_num)
  simp only [iteratedDeriv_zero] at hu
  have hupper : |iteratedDeriv 3 F (3/2)| ≤ (Tsrc/T)*(3*Usrc/σsrc) := by
    rw [hd,abs_mul,abs_of_pos (div_pos hTsrc hT)]
    exact mul_le_mul_of_nonneg_left hu (div_pos hTsrc hT).le
  have hh := hlow.trans ((le_abs_self _).trans hupper)
  have he : (Tsrc/T)*(3*Usrc/σsrc)=3*Usrc*Tsrc/(σsrc*T) := by ring
  rw [he] at hh
  have hc := (le_div_iff₀ (mul_pos hσsrc hT)).mp hh
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 3) hUsrc)).mpr
  nlinarith only [hc]

/-- The same source and model phases yield a physical curvature band
scaled by T, with the Tsrc lower comparison derived from their jets. -/
theorem positive_difference_model_normalized_curvature_band
    (Fsrc : ℝ → ℝ) {σsrc csrc Usrc η y₀ Tsrc T E M σ δ : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy₀ : y₀∈Icc (1:ℝ) 2)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hM : 0 < M) (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hscale : Tsrc ≤ E*T)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) :
    let F := fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y₀))/(σsrc*η)
    Expdb.IsApproximateModelPhaseFunction F σ 2 δ →
    let f := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
    ∀ y∈Icc (1:ℝ) 2, ∀ z∈Icc M (2*M),
      csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2) ≤
        |iteratedDeriv 2 (f y) z/2| ∧
      |iteratedDeriv 2 (f y) z/2| ≤ (3*Usrc/σsrc)*E*T/(2*M^2) := by
  intro F hF f y hy z hz
  have hsource := positive_difference_approximate_model_source_amplitude Fsrc
    hσsrc hUsrc hη hηmax hy₀ hTsrc hT hσ hδ hreg hjets hF
  have hh := positive_difference_half_curvature_source_bounds Fsrc
    hσsrc hcsrc hUsrc hη hηmax hTsrc hM hy hz hreg hjets htests
  constructor
  · apply le_trans _ hh.1
    calc
      _ = (csrc/(4*σsrc*M^2))*(modelPhaseThirdLower σ*σsrc*T/(3*Usrc)) := by
        field_simp
        ring
      _ ≤ (csrc/(4*σsrc*M^2))*Tsrc :=
        mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = _ := by ring
  · apply hh.2.trans
    simpa only [mul_assoc] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (by positivity : (0:ℝ) ≤ 3*Usrc/σsrc))
      (by positivity : (0:ℝ) ≤ 2*M^2)

example
    (Fsrc : ℝ → ℝ) {σsrc Usrc η y Tsrc T σ δ : ℝ}
    (hσsrc : 0 < σsrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy : y∈Icc (1:ℝ) 2)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc) :
    let F := fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y))/(σsrc*η)
    Expdb.IsApproximateModelPhaseFunction F σ 2 δ →
      modelPhaseThirdLower σ*σsrc*T/(3*Usrc) ≤ Tsrc :=
  HuxleyTriangularRegimeScratch.positive_difference_approximate_model_source_amplitude Fsrc (σsrc:=σsrc) (Usrc:=Usrc) (η:=η) (y:=y) (Tsrc:=Tsrc) (T:=T) (σ:=σ) (δ:=δ) hσsrc hUsrc hη hηmax hy hTsrc hT hσ hδ hreg hjets

example
    (Fsrc : ℝ → ℝ) {σsrc csrc Usrc η y₀ Tsrc T E M σ δ : ℝ}
    (hσsrc : 0 < σsrc) (hcsrc : 0 < csrc) (hUsrc : 0 < Usrc)
    (hη : 0 < η) (hηmax : η ≤ 1/8) (hy₀ : y₀∈Icc (1:ℝ) 2)
    (hTsrc : 0 < Tsrc) (hT : 0 < T) (hM : 0 < M) (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1) (hscale : Tsrc ≤ E*T)
    (hreg : ∀ w, 0 < w → ContDiffAt ℝ ∞ Fsrc w)
    (hjets : ∀ w∈Icc (1/2:ℝ) 3, ∀ n ≤ 6, |iteratedDeriv (n+1) Fsrc w| ≤ Usrc)
    (htests : ∀ w∈Icc (1/2:ℝ) 3, ∀ j,
      csrc ≤ |HuxleyModel.tests (fun i : Fin 4 => iteratedDeriv (i.val+3) Fsrc w) j|) :
    let F := fun u => (Tsrc/T)*(Fsrc u-Fsrc (u+η*y₀))/(σsrc*η)
    Expdb.IsApproximateModelPhaseFunction F σ 2 δ →
    let f := fun y z => Tsrc*(Fsrc (z/M)-Fsrc (z/M+η*y))/(σsrc*η)
    ∀ y∈Icc (1:ℝ) 2, ∀ z∈Icc M (2*M),
      csrc*modelPhaseThirdLower σ*T/(12*Usrc*M^2) ≤
        |iteratedDeriv 2 (f y) z/2| ∧
      |iteratedDeriv 2 (f y) z/2| ≤ (3*Usrc/σsrc)*E*T/(2*M^2) :=
  HuxleyTriangularRegimeScratch.positive_difference_model_normalized_curvature_band Fsrc (σsrc:=σsrc) (csrc:=csrc) (Usrc:=Usrc) (η:=η) (y₀:=y₀) (Tsrc:=Tsrc) (T:=T) (E:=E) (M:=M) (σ:=σ) (δ:=δ) hσsrc hcsrc hUsrc hη hηmax hy₀ hTsrc hT hM hσ hδ hscale hreg hjets htests


private theorem triangular_physical_regime_costs
    {M N R U L : ℝ} (hM : 0 < M) (hN : 0 < N) (hR : 0 < R)
    (hU : 0 < U) (hL : 0 ≤ L) (hRN : R ≤ N)
    (hselected : U ≤ (N/R)^((2:ℝ)/3))
    (hregime : N^4 ≤ M*R^3*L^((3:ℝ)/2)) :
    (M^2/N^4)*(M/(N*R^2))^2 ≤ ((M^2/(N^4*U))*L)^3 ∧
    (R^4/N^2)*(N*R^2/M)^2 ≤ ((R^4/(N^2*U))*L)^3 ∧
    M/(N*R^2) ≤ (M^2/(N^4*U))*L^((3:ℝ)/2) ∧
    N*R^2/M ≤ (R^4/(N^2*U))*L^((3:ℝ)/2) := by
  obtain ⟨hfirst,hshort⟩ := triangular_translation_source_regime
    hM hN hR hU.le hL hRN hselected hregime
  have hcore : N^6*U^3 ≤ M^2*R^4*L^3 := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ N^2*U) hfirst 3
    simp only [mul_pow,two_thirds_cube (by positivity : (0:ℝ) ≤ M*R^2)] at hh
    convert hh using 1 <;> ring
  refine ⟨?_,?_,?_,?_⟩
  · rw [show (M^2/N^4)*(M/(N*R^2))^2=M^4/(N^6*R^4) by field_simp,
      show ((M^2/(N^4*U))*L)^3=M^6*L^3/(N^12*U^3) by field_simp]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hcore (by positivity : (0:ℝ) ≤ M^4*N^6)
    nlinarith only [hh]
  · rw [show (R^4/N^2)*(N*R^2/M)^2=R^8/M^2 by field_simp,
      show ((R^4/(N^2*U))*L)^3=R^12*L^3/(N^6*U^3) by field_simp]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hcore (by positivity : (0:ℝ) ≤ R^8)
    nlinarith only [hh]
  · rw [show (M^2/(N^4*U))*L^((3:ℝ)/2)=M^2*L^((3:ℝ)/2)/(N^4*U) by ring]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hshort (by positivity : (0:ℝ) ≤ M*N)
    nlinarith only [hh]
  · rw [show (R^4/(N^2*U))*L^((3:ℝ)/2)=R^4*L^((3:ℝ)/2)/(N^2*U) by ring]
    apply (div_le_div_iff₀ hM (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hshort (sq_nonneg R)
    nlinarith only [hh]


private theorem triangular_weight_regime_absorption
    {Aconst Dconst Bconst abase dbase Cost L : ℝ}
    (hAconst : 0 ≤ Aconst) (hDconst : 0 ≤ Dconst)
    (habase : 0 ≤ abase) (hdbase : 0 ≤ dbase)
    (hCost : 0 ≤ Cost) (hL : 0 ≤ L)
    (hD : 1 ≤ Dconst*dbase)
    (hcubeBase : abase*dbase^2 ≤ (Cost*L)^3)
    (hshortBase : dbase ≤ Cost*L^((3:ℝ)/2)) :
    3*(Aconst*abase)^((3:ℝ)⁻¹)*(Dconst*dbase+2)^((2:ℝ)/3)+
        2*(Bconst*Cost)*(3+2*Real.log (Dconst*dbase+2))+
        (1/2:ℝ)*(2*(Dconst*dbase)+1) ≤
      Cost*(9*(Aconst*Dconst^2)^((3:ℝ)⁻¹)*L+
        2*Bconst*(3+2*Real.log (Dconst*dbase+2))+
        (3/2:ℝ)*Dconst*L^((3:ℝ)/2)) := by
  have hrootCube (z : ℝ) (hz : 0 ≤ z) : (z^((3:ℝ)⁻¹))^3=z := by
    simpa only [Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hz (by norm_num : (3:ℕ)≠0)
  have hDnonneg : 0 ≤ Dconst*dbase := mul_nonneg hDconst hdbase
  have hthree : Dconst*dbase+2 ≤ 3*(Dconst*dbase) := by linarith only [hD]
  have hcube :
      ((Aconst*abase)^((3:ℝ)⁻¹)*(Dconst*dbase+2)^((2:ℝ)/3))^3 ≤
        (3*(Aconst*Dconst^2)^((3:ℝ)⁻¹)*Cost*L)^3 := by
    calc
      _ = (Aconst*abase)*(Dconst*dbase+2)^2 := by
        rw [mul_pow,hrootCube (Aconst*abase) (mul_nonneg hAconst habase),
          two_thirds_cube (by positivity)]
      _ ≤ (Aconst*abase)*(3*(Dconst*dbase))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hthree 2) (mul_nonneg hAconst habase)
      _ = 9*(Aconst*Dconst^2)*(abase*dbase^2) := by ring
      _ ≤ 9*(Aconst*Dconst^2)*(Cost*L)^3 :=
        mul_le_mul_of_nonneg_left hcubeBase (by positivity)
      _ ≤ 27*(Aconst*Dconst^2)*(Cost*L)^3 := by
        have hh : 0 ≤ (Aconst*Dconst^2)*(Cost*L)^3 := by positivity
        nlinarith only [hh]
      _ = _ := by
        simp only [mul_pow,hrootCube (Aconst*Dconst^2) (mul_nonneg hAconst (sq_nonneg Dconst))]
        ring
  have hroot := (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (by norm_num : (3:ℕ)≠0)).mp hcube
  have hroot3 := mul_le_mul_of_nonneg_left hroot (by norm_num : (0:ℝ) ≤ 3)
  have hshort : (1/2:ℝ)*(2*(Dconst*dbase)+1) ≤
      Cost*((3/2:ℝ)*Dconst*L^((3:ℝ)/2)) := by
    have hh := mul_le_mul_of_nonneg_left hshortBase hDconst
    nlinarith only [hD,hh]
  calc
    _ ≤ 3*(3*(Aconst*Dconst^2)^((3:ℝ)⁻¹)*Cost*L)+
        2*(Bconst*Cost)*(3+2*Real.log (Dconst*dbase+2))+
        Cost*((3/2:ℝ)*Dconst*L^((3:ℝ)/2)) :=
      by simpa only [mul_assoc] using add_le_add (add_le_add hroot3 (le_refl (2*(Bconst*Cost)*(3+2*Real.log (Dconst*dbase+2))))) hshort
    _ = _ := by ring


private theorem triangular_source_weight_scale_identities
    {M N R U T σsrc csrc Usrc κ Lunit E θ CU CL DU DL Cthird B : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hR : 0 < R) (hT : 0 < T)
    (hscale : T*N*R^2=M^3) :
    let lambda := csrc*κ*T/(12*Usrc*M^2)
    let Uband := (3*Usrc/σsrc)*E*T/(2*M^2)
    let Aupper := 2*CU*(Cthird+1)*E^2*M^2/(κ*Lunit^3*N^4)
    let Bupper := CU*(Cthird+1)*E^2*M^2/(Lunit^2*N^4*U)+DU*(B+1)*E^2*M^2/(4*N^4*U)
    let Alower := 8*CL*(Cthird+1)*R^4/(κ*Lunit^3*N^2)
    let Blower := 4*CL*(Cthird+1)*R^4/(Lunit^2*N^2*U)+(4*DL*(B+1)*R^4)/(4*N^2*U)
    let AupperConst := 2*CU*(Cthird+1)*E^2/(κ*Lunit^3)
    let BupperConst := CU*(Cthird+1)*E^2/Lunit^2+DU*(B+1)*E^2/4
    let AlowerConst := 8*CL*(Cthird+1)/(κ*Lunit^3)
    let BlowerConst := 4*CL*(Cthird+1)/Lunit^2+DL*(B+1)
    let DupperConst := θ*(3*Usrc/σsrc)*E/2
    let DlowerConst := 12*Usrc*θ/(csrc*κ)
    Aupper=AupperConst*(M^2/N^4) ∧
    Bupper=BupperConst*(M^2/(N^4*U)) ∧
    Alower=AlowerConst*(R^4/N^2) ∧
    Blower=BlowerConst*(R^4/(N^2*U)) ∧
    θ*Uband=DupperConst*(M/(N*R^2)) ∧
    θ/lambda=DlowerConst*(N*R^2/M) := by
  intro lambda Uband Aupper Bupper Alower Blower AupperConst BupperConst
    AlowerConst BlowerConst DupperConst DlowerConst
  have hforward : T/M^2=M/(N*R^2) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    nlinarith only [hscale]
  have hreverse : M^2/T=N*R^2/M := by
    apply (div_eq_div_iff hT.ne' hM.ne').mpr
    nlinarith only [hscale]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · dsimp only [Aupper,AupperConst]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · dsimp only [Bupper,BupperConst]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · dsimp only [Alower,AlowerConst]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · dsimp only [Blower,BlowerConst]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · calc
      _ = DupperConst*(T/M^2) := by dsimp only [Uband,DupperConst]; ring
      _ = _ := by rw [hforward]
  · calc
      _ = DlowerConst*(M^2/T) := by
        dsimp only [lambda,DlowerConst]
        simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
        ring
      _ = _ := by rw [hreverse]

end HuxleyTriangularRegimeScratch
#print axioms HuxleyTriangularRegimeScratch.two_thirds_cube
#print axioms HuxleyTriangularRegimeScratch.triangular_translation_source_regime
#print axioms HuxleyTriangularRegimeScratch.positive_difference_approximate_model_source_amplitude
#print axioms HuxleyTriangularRegimeScratch.positive_difference_model_normalized_curvature_band
#print axioms HuxleyTriangularRegimeScratch.triangular_physical_regime_costs
#print axioms HuxleyTriangularRegimeScratch.triangular_weight_regime_absorption
#print axioms HuxleyTriangularRegimeScratch.triangular_source_weight_scale_identities
