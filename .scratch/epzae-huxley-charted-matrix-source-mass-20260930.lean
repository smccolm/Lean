import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators
namespace HuxleyMatrixSourceScratch

private theorem physical_source_quartic_constants_nonneg
    {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 ≤ δ) :
    0 ≤ quarticReciprocalConstant σ δ ∧ 0 ≤ quarticNonlinearResidualConstant σ δ := by
  have hκ := modelPhaseThirdLower_pos hσ
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ
  have hC₄ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 4) hδ
  constructor
  · dsimp only [quarticReciprocalConstant]
    positivity
  · dsimp only [quarticNonlinearResidualConstant]
    positivity

private theorem mobius_upper_right_large_action_comparison
    {a b c d x y lambda H : ℝ}
    (hlambda : 0 ≤ lambda)
    (hdet : a*d-b*c=1) (htl : (1:ℝ)/2 ≤ c*x+d) (htu : c*x+d ≤ 2)
    (hmap : (a*x+b)/(c*x+d)=y)
    (hx : lambda ≤ |x| ∧ |x| ≤ H) (hy : lambda ≤ |y| ∧ |y| ≤ H)
    (hlarge : 8*H ≤ |c| *lambda^2) :
    |c| *lambda^2/2 ≤ |b| ∧ |b| ≤ (3/2)*|c| *H^2 := by
  let t := c*x+d
  have ht : 0 < t := by dsimp only [t]; linarith only [htl]
  have hH : 0 ≤ H := (abs_nonneg x).trans hx.2
  have he := (div_eq_iff ht.ne').mp hmap
  have ha : a=c*y+1/t := by
    have hid : (a-c*y)*t=1 := by
      dsimp only [t]
      nlinarith only [hdet,congrArg (fun z : ℝ => c*z) he]
    have hh : a-c*y=1/t := (eq_div_iff ht.ne').mpr hid
    linarith only [hh]
  have herrorId : b+c*x*y=t*y-x/t := by
    rw [ha] at he
    change (c*y+1/t)*x+b=y*t at he
    linear_combination he
  have htInv : 1/t ≤ 2 := by
    apply (div_le_iff₀ ht).mpr
    change (1:ℝ)/2 ≤ t at htl
    linarith only [htl]
  have herror : |b+c*x*y| ≤ 4*H := by
    rw [herrorId]
    calc
      _ ≤ |t*y|+|x/t| := abs_sub _ _
      _ = t*|y|+(1/t)*|x| := by
        rw [abs_mul,abs_div,abs_of_pos ht]
        ring
      _ ≤ 2*H+2*H := add_le_add
        (mul_le_mul htu hy.2 (abs_nonneg y) (by norm_num))
        (mul_le_mul htInv hx.2 (abs_nonneg x) (by norm_num))
      _ = _ := by ring
  have hprod : |c*x*y|=|c| *|x| *|y| := by rw [abs_mul,abs_mul]
  have hlo : |c| *lambda^2 ≤ |c*x*y| := by
    rw [hprod]
    have hh := mul_le_mul hx.1 hy.1 hlambda (abs_nonneg x)
    nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg c)]
  have hhi : |c*x*y| ≤ |c| *H^2 := by
    rw [hprod]
    have hh := mul_le_mul hx.2 hy.2 (abs_nonneg y) hH
    nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg c)]
  have hlowTri : |c*x*y| ≤ |b+c*x*y|+|b| := by
    calc
      _ = |(b+c*x*y)-b| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  have hhighTri : |b| ≤ |b+c*x*y|+|c*x*y| := by
    calc
      _ = |(b+c*x*y)-(c*x*y)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  constructor
  · nlinarith only [hlo,hlowTri,herror,hlarge]
  · nlinarith only [hlo,hhi,hhighTri,herror,hlarge]

private theorem mobius_reciprocal_entry_bounds
    {a b c d x y lambda : ℝ}
    (hlambda : 0 < lambda)
    (hdet : a*d-b*c=1) (ht : c*x+d ≠ 0)
    (hmap : (a*x+b)/(c*x+d)=y)
    (hx : lambda ≤ |x|) (hy : lambda ≤ |y|)
    (hnumlo : (1:ℝ)/2 ≤ (a*x+b)/x)
    (hnumhi : (a*x+b)/x ≤ 2) :
    |a| ≤ |b|/lambda+2 ∧ |d| ≤ |b|/lambda+2 := by
  have hx0 : x ≠ 0 := abs_pos.mp (hlambda.trans_le hx)
  have hy0 : y ≠ 0 := abs_pos.mp (hlambda.trans_le hy)
  have he := (div_eq_iff ht).mp hmap
  have hden : b*(1/x)+a=(a*x+b)/x := by
    field_simp [hx0]
    ring
  have hdenp : 0 < b*(1/x)+a := by rw [hden]; linarith only [hnumlo]
  have hrmap : (d*(1/x)+c)/(b*(1/x)+a)=1/y := by
    apply (div_eq_iff hdenp.ne').mpr
    field_simp [hx0,hy0]
    nlinarith only [he]
  have hrx : |1/x| ≤ 1/lambda := by
    rw [abs_div,abs_one]
    exact one_div_le_one_div_of_le hlambda hx
  have hry : |1/y| ≤ 1/lambda := by
    rw [abs_div,abs_one]
    exact one_div_le_one_div_of_le hlambda hy
  have hh := bourgain_mobius_entry_bounds
    (a:=d) (b:=c) (c:=b) (d:=a) (x:=1/x) (y:=1/y)
    (by nlinarith only [hdet]) (by rw [hden]; exact hnumlo)
    (by rw [hden]; exact hnumhi) hrmap hrx hry
  constructor
  · simpa only [mul_one_div] using hh.2
  · simpa only [mul_one_div] using hh.1

private theorem resonance_matrix_reciprocal_sum
    (S : Finset (Fin 4 → ℤ)) {X Gamma : ℝ}
    (hX : 0 ≤ X) (hGamma : 0 ≤ Gamma)
    (hdet : ∀ M∈S, M 0*M 3-M 1*M 2=1)
    (hc : ∀ M∈S, M 2 ≠ 0 ∧ |(M 2:ℝ)| ≤ Gamma)
    (ha : ∀ M∈S, |(M 0:ℝ)| ≤ |(M 2:ℝ)| *X+2)
    (hd : ∀ M∈S, |(M 3:ℝ)| ≤ |(M 2:ℝ)| *X+2) :
    ∑ M∈S,1/|(M 2:ℝ)| ≤ (2*Gamma+1)*(2*X+5)^2 := by
  let Z := ∑ M∈S,1/|(M 2:ℝ)|
  let K := (2*Gamma+1)*(2*X+5)^2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  by_contra! hbad
  have hgap : 0 < Z-K := sub_pos.mpr hbad
  let W := (K*Gamma+1)/(Z-K)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hh := bourgain_resonance_matrix_weight_sum S hX hGamma hW hdet hc ha hd
  have he : (∑ M∈S,(1+W/|(M 2:ℝ)|))=(S.card:ℝ)+W*Z := by
    dsimp only [Z]
    simp only [Finset.sum_add_distrib,div_eq_mul_inv,←Finset.mul_sum,
      Finset.sum_const,nsmul_eq_mul,mul_one,one_mul]
  rw [he] at hh
  have hw : W*(Z-K)=K*Gamma+1 := by dsimp only [W]; field_simp
  change (S.card:ℝ)+W*Z ≤ K*(Gamma+W) at hh
  nlinarith only [hh,hw,(show (0:ℝ) ≤ S.card from Nat.cast_nonneg _)]



private theorem cubic_reciprocal_majorant {K c Gamma : ℝ}
    (hK : 0 ≤ K) (hc : 0 < c) (hcap : c ≤ Gamma) :
    (K/c)^((3:ℝ)⁻¹) ≤ K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)/c := by
  apply (le_div_iff₀ hc).mpr
  calc
    _ = K^((3:ℝ)⁻¹)*c^(1-(3:ℝ)⁻¹) := by
      rw [Real.div_rpow hK hc.le,Real.rpow_sub hc,Real.rpow_one]
      ring
    _ ≤ K^((3:ℝ)⁻¹)*Gamma^(1-(3:ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc.le hcap (by norm_num))
        (Real.rpow_nonneg hK _)
    _ = _ := by norm_num

private theorem resonance_matrix_cubic_weight_sum
    (S : Finset (Fin 4 → ℤ)) {Vbound Gamma A K B : ℝ}
    (hV : 0 ≤ Vbound) (hGamma : 0 ≤ Gamma)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gamma)
    (ha : ∀ Mat∈S, |(Mat 0:ℝ)| ≤ |(Mat 2:ℝ)| *Vbound+2)
    (hd : ∀ Mat∈S, |(Mat 3:ℝ)| ≤ |(Mat 2:ℝ)| *Vbound+2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      ((2*Gamma+1)*(2*Vbound+5)^2)*(A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B) := by
  have hw := resonance_matrix_reciprocal_sum S hV hGamma hdet hc ha hd
  have hp Mat (hMat : Mat∈S) : 0 < |(Mat 2:ℝ)| :=
    abs_pos.mpr (by exact_mod_cast (hc Mat hMat).1)
  let C := A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hK _))
      (Real.rpow_nonneg hGamma _)) hB
  calc
    _ ≤ ∑ Mat∈S,C*(1/|(Mat 2:ℝ)|) := by
      apply Finset.sum_le_sum
      intro Mat hMat
      have hh := mul_le_mul_of_nonneg_left
        (cubic_reciprocal_majorant hK (hp Mat hMat) (hc Mat hMat).2) hA
      dsimp only [C]
      calc
        _ ≤ A*(K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)/|(Mat 2:ℝ)|)+B/|(Mat 2:ℝ)| :=
          add_le_add hh le_rfl
        _ = _ := by ring
    _ = C*(∑ Mat∈S,1/|(Mat 2:ℝ)|) := (Finset.mul_sum S _ _).symm
    _ ≤ C*((2*Gamma+1)*(2*Vbound+5)^2) := mul_le_mul_of_nonneg_left hw hC
    _ = _ := by dsimp only [C]; ring



private theorem resonance_matrix_reciprocal_cubic_weight_sum
    (S : Finset (Fin 4 → ℤ)) {X Gamma Theta A K B : ℝ}
    (hX : 0 ≤ X) (hGamma : 0 ≤ Gamma) (hTheta : 0 ≤ Theta)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0)
    (hb : ∀ Mat∈S, Mat 1 ≠ 0 ∧ |(Mat 1:ℝ)| ≤ Gamma)
    (hcompare : ∀ Mat∈S, |(Mat 1:ℝ)| ≤ Theta*|(Mat 2:ℝ)|)
    (ha : ∀ Mat∈S, |(Mat 0:ℝ)| ≤ |(Mat 1:ℝ)| *X+2)
    (hd : ∀ Mat∈S, |(Mat 3:ℝ)| ≤ |(Mat 1:ℝ)| *X+2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      ((2*Gamma+1)*(2*X+5)^2)*
        (A*(Theta*K)^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+Theta*B) := by
  classical
  let flip := fun Mat : Fin 4 → ℤ => (![Mat 3,Mat 2,Mat 1,Mat 0] : Fin 4 → ℤ)
  have hflip Mat : flip (flip Mat)=Mat := by
    funext i
    fin_cases i <;> rfl
  have hinj : Function.Injective flip := by
    intro Mat Mat' he
    have hh := congrArg flip he
    rw [hflip,hflip] at hh
    exact hh
  have hw := resonance_matrix_cubic_weight_sum (S.image flip)
    hX hGamma hA (mul_nonneg hTheta hK) (mul_nonneg hTheta hB)
    (by
      intro W hW
      obtain ⟨Mat,hMat,rfl⟩ := Finset.mem_image.mp hW
      change Mat 3*Mat 0-Mat 2*Mat 1=1
      nlinarith only [hdet Mat hMat])
    (by
      intro W hW
      obtain ⟨Mat,hMat,rfl⟩ := Finset.mem_image.mp hW
      exact hb Mat hMat)
    (by
      intro W hW
      obtain ⟨Mat,hMat,rfl⟩ := Finset.mem_image.mp hW
      exact hd Mat hMat)
    (by
      intro W hW
      obtain ⟨Mat,hMat,rfl⟩ := Finset.mem_image.mp hW
      exact ha Mat hMat)
  rw [Finset.sum_image hinj.injOn] at hw
  apply le_trans _ hw
  apply Finset.sum_le_sum
  intro Mat hMat
  have hcp : 0 < |(Mat 2:ℝ)| := abs_pos.mpr (by exact_mod_cast hc Mat hMat)
  have hbp : 0 < |(Mat 1:ℝ)| := abs_pos.mpr (by exact_mod_cast (hb Mat hMat).1)
  have hKbound : K/|(Mat 2:ℝ)| ≤ (Theta*K)/|(Mat 1:ℝ)| := by
    apply (div_le_div_iff₀ hcp hbp).mpr
    nlinarith only [mul_le_mul_of_nonneg_left (hcompare Mat hMat) hK]
  have hBbound : B/|(Mat 2:ℝ)| ≤ (Theta*B)/|(Mat 1:ℝ)| := by
    apply (div_le_div_iff₀ hcp hbp).mpr
    nlinarith only [mul_le_mul_of_nonneg_left (hcompare Mat hMat) hB]
  exact add_le_add (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (div_nonneg hK hcp.le) hKbound (by norm_num)) hA) hBbound

private theorem resonance_matrix_curvature_band_cubic_weight_sum
    (S : Finset (Fin 4 → ℤ)) (x y : (Fin 4 → ℤ) → ℝ)
    {lambda H Gamma A K B : ℝ}
    (hlambda : 0 < lambda) (hGamma : 0 ≤ Gamma)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hdet : ∀ Mat∈S, Mat 0*Mat 3-Mat 1*Mat 2=1)
    (hc : ∀ Mat∈S, Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gamma)
    (hx : ∀ Mat∈S, lambda ≤ |x Mat| ∧ |x Mat| ≤ H)
    (hy : ∀ Mat∈S, lambda ≤ |y Mat| ∧ |y Mat| ≤ H)
    (ht : ∀ Mat∈S, (1:ℝ)/2 ≤ (Mat 2:ℝ)*x Mat+Mat 3 ∧
      (Mat 2:ℝ)*x Mat+Mat 3 ≤ 2)
    (hmap : ∀ Mat∈S, ((Mat 0:ℝ)*x Mat+Mat 1)/
      ((Mat 2:ℝ)*x Mat+Mat 3)=y Mat)
    (hnum : ∀ Mat∈S, (1:ℝ)/2 ≤ ((Mat 0:ℝ)*x Mat+Mat 1)/x Mat ∧
      ((Mat 0:ℝ)*x Mat+Mat 1)/x Mat ≤ 2)
    (hlarge : ∀ Mat∈S, 8*H ≤ |(Mat 2:ℝ)| *lambda^2) :
    ∑ Mat∈S,(A*(K/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+B/|(Mat 2:ℝ)|) ≤
      588*(H/lambda)^2*H^2*Gamma*
        (A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B) := by
  classical
  let E := A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3)+B
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hFactor {g v : ℝ} (hg : 1 ≤ g) (hv : 1 ≤ v) :
      (2*g+1)*(2*v+5)^2 ≤ 147*g*v^2 := by
    have hg0 : 0 ≤ g := zero_le_one.trans hg
    have hv0 : 0 ≤ v := zero_le_one.trans hv
    have hgl : 2*g+1 ≤ 3*g := by linarith only [hg]
    have hvl : 2*v+5 ≤ 7*v := by linarith only [hv]
    have hvp := pow_le_pow_left₀ (by positivity : 0 ≤ 2*v+5) hvl 2
    have hh := mul_le_mul hgl hvp (sq_nonneg _) (by positivity : 0 ≤ 3*g)
    nlinarith only [hh]
  by_cases hS : S.Nonempty
  · obtain ⟨Mat₀,hMat₀⟩ := hS
    have hLH : lambda ≤ H := (hx Mat₀ hMat₀).1.trans (hx Mat₀ hMat₀).2
    have hH : 0 < H := hlambda.trans_le hLH
    have hGammaOne : 1 ≤ Gamma :=
      (show (1:ℝ) ≤ |(Mat₀ 2:ℝ)| by exact_mod_cast Int.one_le_abs (hc Mat₀ hMat₀).1).trans
        (hc Mat₀ hMat₀).2
    have hcp Mat (hMat : Mat∈S) : 0 < |(Mat 2:ℝ)| :=
      abs_pos.mpr (by exact_mod_cast (hc Mat hMat).1)
    have hdetR Mat (hMat : Mat∈S) :
        (Mat 0:ℝ)*Mat 3-(Mat 1:ℝ)*Mat 2=1 := by exact_mod_cast hdet Mat hMat
    by_cases hWide : 1 ≤ H
    · have hentries Mat (hMat : Mat∈S) :=
        bourgain_mobius_entry_bounds (hdetR Mat hMat) (ht Mat hMat).1 (ht Mat hMat).2
          (hmap Mat hMat) (hx Mat hMat).2 (hy Mat hMat).2
      have hw := resonance_matrix_cubic_weight_sum S hH.le hGamma hA hK hB hdet hc
        (fun Mat hMat => (hentries Mat hMat).1) (fun Mat hMat => (hentries Mat hMat).2)
      have hratio : 1 ≤ H/lambda := (le_div_iff₀ hlambda).mpr (by simpa using hLH)
      have hsquare : 1 ≤ (H/lambda)^2 := by nlinarith only [hratio,sq_nonneg (H/lambda-1)]
      have hscale := mul_le_mul_of_nonneg_right hsquare (sq_nonneg H)
      have hmul := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 147*Gamma by positivity)
      have hpos : 0 ≤ (H/lambda)^2*H^2*Gamma := by positivity
      have hfac : 147*Gamma*H^2 ≤ 588*(H/lambda)^2*H^2*Gamma := by
        nlinarith only [hmul,hpos]
      exact hw.trans ((mul_le_mul_of_nonneg_right (hFactor hGammaOne hWide) hE).trans
        (mul_le_mul_of_nonneg_right hfac hE))
    · let Theta := 2*H^2
      let G := Theta*Gamma
      have hTheta : 0 < Theta := by dsimp only [Theta]; positivity
      have hG : 0 ≤ G := mul_nonneg hTheta.le hGamma
      have hcompare Mat (hMat : Mat∈S) : |(Mat 1:ℝ)| ≤ Theta*|(Mat 2:ℝ)| := by
        have hh := mobius_upper_right_large_action_comparison hlambda.le
          (hdetR Mat hMat) (ht Mat hMat).1 (ht Mat hMat).2 (hmap Mat hMat)
          (hx Mat hMat) (hy Mat hMat) (hlarge Mat hMat)
        have hp := mul_nonneg (abs_nonneg (Mat 2:ℝ)) (sq_nonneg H)
        dsimp only [Theta]
        nlinarith only [hh.2,hp]
      have hb Mat (hMat : Mat∈S) : Mat 1 ≠ 0 ∧ |(Mat 1:ℝ)| ≤ G := by
        have hh := mobius_upper_right_large_action_comparison hlambda.le
          (hdetR Mat hMat) (ht Mat hMat).1 (ht Mat hMat).2 (hmap Mat hMat)
          (hx Mat hMat) (hy Mat hMat) (hlarge Mat hMat)
        have hcpos := hcp Mat hMat
        have hp : 0 < |(Mat 1:ℝ)| :=
          (show 0 < |(Mat 2:ℝ)| *lambda^2/2 by positivity).trans_le hh.1
        refine ⟨?_,(hcompare Mat hMat).trans
          (mul_le_mul_of_nonneg_left (hc Mat hMat).2 hTheta.le)⟩
        exact_mod_cast abs_pos.mp hp
      have hentries Mat (hMat : Mat∈S) :=
        mobius_reciprocal_entry_bounds hlambda (hdetR Mat hMat)
          (show (Mat 2:ℝ)*x Mat+Mat 3 ≠ 0 by linarith only [(ht Mat hMat).1])
          (hmap Mat hMat) (hx Mat hMat).1 (hy Mat hMat).1
          (hnum Mat hMat).1 (hnum Mat hMat).2
      have hw := resonance_matrix_reciprocal_cubic_weight_sum S
        (show 0 ≤ 1/lambda by positivity) hG hTheta.le hA hK hB hdet
        (fun Mat hMat => (hc Mat hMat).1) hb hcompare
        (fun Mat hMat => by simpa only [mul_one_div] using (hentries Mat hMat).1)
        (fun Mat hMat => by simpa only [mul_one_div] using (hentries Mat hMat).2)
      have hGOne : 1 ≤ G :=
        (show (1:ℝ) ≤ |(Mat₀ 1:ℝ)| by exact_mod_cast Int.one_le_abs (hb Mat₀ hMat₀).1).trans
          (hb Mat₀ hMat₀).2
      have hInv : 1 ≤ 1/lambda := (le_div_iff₀ hlambda).mpr
        (by linarith only [hLH,le_of_not_ge hWide])
      have hpow : Theta^((3:ℝ)⁻¹)*Theta^((2:ℝ)/3)=Theta := by
        rw [←Real.rpow_add hTheta]
        norm_num
      have he : A*(Theta*K)^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+Theta*B=Theta*E := by
        dsimp only [G,E]
        rw [Real.mul_rpow hTheta.le hK,Real.mul_rpow hTheta.le hGamma]
        calc
          _ = (Theta^((3:ℝ)⁻¹)*Theta^((2:ℝ)/3))*
              (A*K^((3:ℝ)⁻¹)*Gamma^((2:ℝ)/3))+Theta*B := by ring
          _ = _ := by rw [hpow]; ring
      rw [he] at hw
      calc
        _ ≤ ((2*G+1)*(2*(1/lambda)+5)^2)*(Theta*E) := hw
        _ ≤ (147*G*(1/lambda)^2)*(Theta*E) :=
          mul_le_mul_of_nonneg_right (hFactor hGOne hInv) (mul_nonneg hTheta.le hE)
        _ = _ := by dsimp only [Theta,G,E]; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.sum_empty]
    change 0 ≤ 588*(H/lambda)^2*H^2*Gamma*E
    positivity


private theorem matrix_sample_mass_weight_majorant
    {mass m K P G R L N U C Gamma : ℝ}
    (hm : 0 ≤ m) (hC : 0 < C) (hcap : C ≤ Gamma)
    (hmass : mass ≤ 4*m*((K/C)^((3:ℝ)⁻¹)+P*R^4/(L^2*N^2*C*U))+
      m*(2+G*R^4/(N^2*C*U))) :
    mass ≤ 4*m*(K/C)^((3:ℝ)⁻¹)+
      (4*m*P*R^4/(L^2*N^2*U)+m*G*R^4/(N^2*U)+2*m*Gamma)/C := by
  have hconstant : 2*m ≤ 2*m*Gamma/C :=
    (le_div_iff₀ hC).mpr (mul_le_mul_of_nonneg_left hcap (mul_nonneg (by norm_num) hm))
  calc
    _ ≤ 4*m*((K/C)^((3:ℝ)⁻¹)+P*R^4/(L^2*N^2*C*U))+
        m*(2+G*R^4/(N^2*C*U)) := hmass
    _ = 4*m*(K/C)^((3:ℝ)⁻¹)+
        (4*m*P*R^4/(L^2*N^2*U)+m*G*R^4/(N^2*U))/C+2*m := by ring
    _ ≤ 4*m*(K/C)^((3:ℝ)⁻¹)+
        (4*m*P*R^4/(L^2*N^2*U)+m*G*R^4/(N^2*U))/C+2*m*Gamma/C :=
      add_le_add le_rfl hconstant
    _ = _ := by ring

private theorem cubic_matrix_source_scale
    {Z k b m U V G : ℝ}
    (hZ : 0 < Z) (hk : 0 ≤ k) (hb : 0 ≤ b) (hm : 0 ≤ m)
    (hU : 0 < U) (hV : 1 ≤ V) (hG : 0 ≤ G) (hcap : G ≤ Z/V) :
    G*(4*m*(k*Z)^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+m*b*Z/U+2*m*G) ≤
      m*Z^2*((4*k^((3:ℝ)⁻¹)+2)/V^((5:ℝ)/3)+b/(U*V)) := by
  have hVp : 0 < V := zero_lt_one.trans_le hV
  have hratio : 0 ≤ Z/V := (div_pos hZ hVp).le
  have hcoeff : 0 ≤ 4*m*(k*Z)^((3:ℝ)⁻¹) := by positivity
  have hinner :
      4*m*(k*Z)^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+m*b*Z/U+2*m*G ≤
      4*m*(k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)+m*b*Z/U+2*m*(Z/V) := by
    exact add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hG hcap (by norm_num)) hcoeff) le_rfl)
      (mul_le_mul_of_nonneg_left hcap (by positivity))
  have hproduct : (k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)=
      k^((3:ℝ)⁻¹)*Z/V^((2:ℝ)/3) := by
    rw [Real.mul_rpow hk hZ.le,Real.div_rpow hZ.le hVp.le]
    have hpow : Z^((3:ℝ)⁻¹)*Z^((2:ℝ)/3)=Z := by
      rw [←Real.rpow_add hZ]
      norm_num
    calc
      _ = k^((3:ℝ)⁻¹)*(Z^((3:ℝ)⁻¹)*Z^((2:ℝ)/3))/V^((2:ℝ)/3) := by ring
      _ = _ := by rw [hpow]
  have hVpow : V*V^((2:ℝ)/3)=V^((5:ℝ)/3) := by
    calc
      _ = V^(1:ℝ)*V^((2:ℝ)/3) := by rw [Real.rpow_one]
      _ = V^((1:ℝ)+2/3) := (Real.rpow_add hVp _ _).symm
      _ = _ := by norm_num
  have hsquare : V^((5:ℝ)/3) ≤ V^2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hV (by norm_num : (5:ℝ)/3 ≤ 2)
    simpa only [Real.rpow_two] using hh
  have htail : 2/V^2 ≤ 2/V^((5:ℝ)/3) :=
    div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hVp _) hsquare
  calc
    _ ≤ (Z/V)*(4*m*(k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)+m*b*Z/U+2*m*(Z/V)) :=
      mul_le_mul hcap hinner (by positivity) hratio
    _ = m*Z^2*(4*k^((3:ℝ)⁻¹)/V^((5:ℝ)/3)+b/(U*V)+2/V^2) := by
      have he : 4*m*(k*Z)^((3:ℝ)⁻¹)*(Z/V)^((2:ℝ)/3)=
          4*m*(k^((3:ℝ)⁻¹)*Z/V^((2:ℝ)/3)) := by rw [←hproduct]; ring
      rw [he,←hVpow]
      ring
    _ ≤ m*Z^2*(4*k^((3:ℝ)⁻¹)/V^((5:ℝ)/3)+b/(U*V)+2/V^((5:ℝ)/3)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl htail) (by positivity)
    _ = _ := by ring



private theorem matrix_physical_source_scale
    {R N L U V Cfirst Cpack Cgap m H lambda : ℝ}
    (hR : 0 < R) (hN : 0 < N) (hL : 0 < L) (hU : 0 < U) (hV : 1 ≤ V)
    (hCf : 0 ≤ Cfirst) (hCp : 0 ≤ Cpack) (hCg : 0 ≤ Cgap) (hm : 0 ≤ m) :
    let G := R^4/(6*N^2*V)
    let K := 2*Cfirst*R^4/(L^3*N^2)
    let B := 4*m*Cpack*R^4/(L^2*N^2*U)+m*Cgap*R^4/(N^2*U)+2*m*G
    588*(H/lambda)^2*H^2*G*(4*m*K^((3:ℝ)⁻¹)*G^((2:ℝ)/3)+B) ≤
      588*m*(H/lambda)^2*H^2*(R^8/N^4)*
        ((4*(2*Cfirst/L^3)^((3:ℝ)⁻¹)+2)/V^((5:ℝ)/3)+
          (4*Cpack/L^2+Cgap)/(U*V)) := by
  intro G K B
  let Z := R^4/N^2
  let k := 2*Cfirst/L^3
  let b := 4*Cpack/L^2+Cgap
  have hVp : 0 < V := zero_lt_one.trans_le hV
  have hZ : 0 < Z := by dsimp only [Z]; positivity
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hcap : G ≤ Z/V := by
    calc
      G = Z/(6*V) := by dsimp only [G,Z]; ring
      _ ≤ Z/V := div_le_div_of_nonneg_left hZ.le hVp (by linarith only [hVp])
  have hh := cubic_matrix_source_scale hZ hk hb hm hU hV hG hcap
  have hK : K=k*Z := by dsimp only [K,k,Z]; ring
  have hB : B=m*b*Z/U+2*m*G := by dsimp only [B,b,Z]; ring
  have hZsquare : Z^2=R^8/N^4 := by dsimp only [Z]; ring
  have hs := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ 588*(H/lambda)^2*H^2 by positivity)
  rw [hK,hB]
  convert hs using 1
  · ring
  · rw [hZsquare]
    dsimp only [k,b]
    ring



private theorem physicalModelPhase_actual_fourier_charted_matrix_source_mass_core
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Matrices : Finset (Fin 4 → ℤ)) (Bmajor Cmajor : ℕ)
    (S : (Fin 4 → ℤ) → ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℚ)
    (vinv : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → Fin 2)
    (anchor : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((x Mat) ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, (((rat Mat) ab) j i).den ≤ Q ∧ Q ≤ 2*(((rat Mat) ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, lambda ≤ |(((rat Mat) ab) j i:ℝ)| ∧ |(((rat Mat) ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((((rat Mat) ab) j i).den:ℤ) ∣ (((rat Mat) ab) j i).num*((vinv Mat) ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (((rat Mat) ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : ∀ Mat∈Matrices, Mat 2 ≠ 0)
    (hlarge : ∀ Mat∈Matrices, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (haction : ∀ Mat∈Matrices, 8*Uband ≤ |(Mat 2:ℝ)| *lambda^2)
    (hV : 1 ≤ V)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊((((rat Mat) ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((((rat Mat) ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((sourceColor Mat) ab) j 0=((sourceColor Mat) ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, iteratedDeriv 2 (f i) (((x Mat) ab) j i)/2=(((rat Mat) ab) j i:ℝ)) →
    let q := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (((rat Mat) ab) j i).den
    let mu := fun Mat => fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round (((x Mat) ab) j i))/6
    let ell := fun Mat => fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round (((x Mat) ab) j i))
    let b := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i⌋+(((parity Mat) ab) j i:ℕ) : ℤ)
    let cround := fun Mat => fun (ab : ℝ × ℝ) => fun j i => round ((((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)
    let tau := fun Mat => fun (ab : ℝ × ℝ) => fun j i => ((((b Mat) ab) j i:ℝ)-(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)/2
    let dual := fun Mat => fun (ab : ℝ × ℝ) => fun j i => -2*((mu Mat) ab) j i*(Real.sqrt (2/(3*((mu Mat) ab) j i*(((q Mat) ab) j i:ℝ))))^3
    let cloud := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-(((vinv Mat) ab) j i:ℝ)*((b Mat) ab) j i/((q Mat) ab) j i),
      Int.fract (-(((vinv Mat) ab) j i:ℝ)/((q Mat) ab) j i),((dual Mat) ab) j i/Real.sqrt K₀,
      (3*((dual Mat) ab) j i*((tau Mat) ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((b Mat) ab) j 0-((cround Mat) ab) j 0=((b Mat) ab) j 1-((cround Mat) ab) j 1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ a, |((cloud Mat) ab) j 0 a-((cloud Mat) ab) j 1 a| ≤ 2*radius a) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈S Mat ab,
      |cloud Mat ab j 0 1-cloud Mat ab j 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ Mat∈Matrices, Mat 0*Mat 3-Mat 1*Mat 2=1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3=(((q Mat) ab) j 1:ℝ)/((q Mat) ab) j 0) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((Mat 0:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3)=(((rat Mat) ab) j 1:ℝ)) →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), |(((anchor Mat) ab) j:ℝ)-(((rat Mat) ab) j 0:ℝ)| ≤ ε) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256*((((anchor Mat) ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*(((anchor Mat) ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Gcap := R^4/(6*N^2*V)
    let Kstar := 2*Cfirst*R^4/(Lunit^3*N^2)
    let Aweight := 4*(m0:ℝ)
    let Bweight := 4*(m0:ℝ)*Cpack*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (m0:ℝ)*Cgap*R^4/(N^2*(Uref:ℝ))+2*(m0:ℝ)*Gcap
    (∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
      588*(Uband/lambda)^2*Uband^2*Gcap*
        (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear hnearNarrow
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Cpack Cfirst Cgap
    Gcap Kstar Aweight Bweight
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hunit : 0 < Lunit := div_pos (mul_pos (by norm_num) hκ) hCphys
  have hm0 : 0 < m0 := by dsimp only [m0]; omega
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  obtain ⟨hCR,hCN⟩ := physical_source_quartic_constants_nonneg hσ hδ0
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hK : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hΓ : 0 ≤ Gamma := div_nonneg hCphys.le hκ.le
  have hCthird : 0 ≤ Cthird :=
    mul_nonneg hΓ (add_nonneg (mul_nonneg (by norm_num) hK)
      (mul_nonneg (by norm_num) hCR))
  have hcore : 0 ≤ Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ :=
    add_nonneg (mul_nonneg (sq_nonneg Gamma) hCthird)
      (div_nonneg (mul_nonneg hΓ hC₃) hκ.le)
  have hCpack : 0 ≤ Cpack :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hcore) hκ.le
  have hCfirst : 0 ≤ Cfirst :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hcore) (sq_nonneg κ)
  have hCgap : 0 ≤ Cgap :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le)
      (add_nonneg (mul_nonneg (sq_nonneg Gamma) hB)
        (div_nonneg (mul_nonneg hΓ hC₃) hκ.le))) hκ.le
  have hVp : 0 < V := zero_lt_one.trans_le hV
  have hGcap : 0 ≤ Gcap := by dsimp only [Gcap]; positivity
  have hKstar : 0 ≤ Kstar := by dsimp only [Kstar]; positivity
  have hAweight : 0 ≤ Aweight := by dsimp only [Aweight]; positivity
  have hBweight : 0 ≤ Bweight := by dsimp only [Bweight]; positivity
  have hK₀ : (1:ℝ) ≤ K₀ := by exact_mod_cast (show 1 ≤ K₀ from NeZero.pos K₀)
  have hmass Mat (hMat : Mat∈Matrices) :
      (∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
        4*(m0:ℝ)*((Kstar/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+
          Cpack*R^4/(Lunit^2*N^2*|(Mat 2:ℝ)| *(Uref:ℝ)))+
        (m0:ℝ)*(2+Cgap*R^4/(N^2*|(Mat 2:ℝ)| *(Uref:ℝ))) := by
    exact physicalModelPhase_actual_fourier_charted_all_reference_sample_mass
      Uref Refs Gaps (Bselect:=Bselect) Bmajor Cmajor (S Mat) Q K₀
      (rat Mat) (vinv Mat) (parity Mat) (anchor Mat) Mat e r v s
      hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW (hx Mat hMat) (hwindow Mat hMat) (hden Mat hMat) hlambda hUband hθ hθmax (hcurv Mat hMat) (hinv Mat hMat) hchart horientation hBcut hs hrefSet hparentSet hsep (hwideL Mat hMat) (hwideU Mat hMat) hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen (hfamilyGap Mat hMat)
      (hc Mat hMat) (hlarge Mat hMat) hgap
      (hsourceColor Mat hMat) (hlevel Mat hMat) (hcolor Mat hMat) (hnear Mat hMat) hsmall hNR hRN hNcube hminscale (hMatdet Mat hMat) (hMatt Mat hMat) (hMatmap Mat hMat) (hMatgamma Mat hMat) hNtwo (hL Mat hMat) (hU Mat hMat) (hanchor Mat hMat) (hcut Mat hMat) (hcount Mat hMat)
      hsize hD hΔ hBsize hBmajor hCmajor
  let Occupied := Matrices.filter (fun Mat => ∃ ab∈Gaps, (S Mat ab).Nonempty)
  have hin : Occupied ⊆ Matrices := Finset.filter_subset _ _
  have hpick Mat (hMat : Mat∈Occupied) : ∃ ab, ab∈Gaps ∧ ∃ j, j∈S Mat ab := by
    obtain ⟨ab,hab,hne⟩ := (Finset.mem_filter.mp hMat).2
    obtain ⟨j,hj⟩ := hne
    exact ⟨ab,hab,j,hj⟩
  choose! ab hab j hj using hpick
  let pr := fun Mat i => rat Mat (ab Mat) (j Mat) i
  have hpden Mat (hMat : Mat∈Occupied) i := hden Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat) i
  have hpcurv Mat (hMat : Mat∈Occupied) i := hcurv Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat) i
  have hpMatt Mat (hMat : Mat∈Occupied) := hMatt Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat)
  have hpmap Mat (hMat : Mat∈Occupied) := hMatmap Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat)
  have hpcap Mat (hMat : Mat∈Occupied) : Mat 2 ≠ 0 ∧ |(Mat 2:ℝ)| ≤ Gcap := by
    have hh := fourier_matrix_narrowed_coordinate_entry_bound
      (fun i => ((pr Mat i).den:ℤ)) (fun i => (pr Mat i).num)
      (vinv Mat (ab Mat) (j Mat)) Mat (Q:=(Q:ℝ)) (K:=(K₀:ℝ)) (V:=V)
      (N:=N) (R:=R)
      (fun i => by
        change (0:ℤ) < ((pr Mat i).den:ℤ)
        exact_mod_cast (pr Mat i).den_pos)
      hK₀ hV hN hmesh
      (fun i => by
        have hlo : ((pr Mat i).den:ℝ) ≤ Q := by exact_mod_cast (hpden Mat hMat i).1
        have hhi : (Q:ℝ) ≤ 2*((pr Mat i).den:ℝ) := by exact_mod_cast (hpden Mat hMat i).2
        simpa only [Int.cast_natCast] using And.intro hlo hhi)
      (hinv Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat))
      (hMatdet Mat (hin hMat))
      (by simpa only [Int.cast_natCast,Rat.cast_def] using hpMatt Mat hMat)
      (by simpa only [Int.cast_natCast,Rat.cast_def] using hpmap Mat hMat)
      (hMatgamma Mat (hin hMat))
      (by
        have hh := hnearNarrow Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat)
        change |Int.fract (-(vinv Mat (ab Mat) (j Mat) 0:ℝ)/(pr Mat 0).den)-
          Int.fract (-(vinv Mat (ab Mat) (j Mat) 1:ℝ)/(pr Mat 1).den)| ≤
            1/(6*(K₀:ℝ)^2*V) at hh
        simpa only [Int.cast_natCast] using hh)
    exact ⟨hc Mat (hin hMat),hh.2⟩
  have hratios Mat (hMat : Mat∈Occupied) :
      |((pr Mat 1).den:ℝ)/(pr Mat 0).den-1| ≤ θ ∧
      |((pr Mat 1).num:ℝ)/(pr Mat 0).num-1| ≤ θ := by
    have hh := (rational_narrow_band_partition Finset.univ (pr Mat) Q
      hQ hlambda hUband hθ (fun i _ => hpcurv Mat hMat i)
      (fun i _ => hpden Mat hMat i)).2
    exact hh 0 (Finset.mem_univ _) 1 (Finset.mem_univ _)
      (hsourceColor Mat (hin hMat) _ (hab Mat hMat) _ (hj Mat hMat))
  have hpt Mat (hMat : Mat∈Occupied) :
      (1:ℝ)/2 ≤ (Mat 2:ℝ)*(pr Mat 0:ℝ)+Mat 3 ∧
      (Mat 2:ℝ)*(pr Mat 0:ℝ)+Mat 3 ≤ 2 := by
    rw [hpMatt Mat hMat]
    have hh := abs_le.mp (hratios Mat hMat).1
    constructor <;> linarith only [hh.1,hh.2,hθmax]
  have hpnum Mat (hMat : Mat∈Occupied) :
      (1:ℝ)/2 ≤ ((Mat 0:ℝ)*(pr Mat 0:ℝ)+Mat 1)/(pr Mat 0:ℝ) ∧
      ((Mat 0:ℝ)*(pr Mat 0:ℝ)+Mat 1)/(pr Mat 0:ℝ) ≤ 2 := by
    have hx0 : (pr Mat 0:ℝ) ≠ 0 := abs_pos.mp (hlambda.trans_le (hpcurv Mat hMat 0).1)
    have hnum0 : ((pr Mat 0).num:ℝ) ≠ 0 := by
      intro hh
      apply hx0
      rw [Rat.cast_def,hh,zero_div]
    have hq0 : (0:ℝ) < (pr Mat 0).den := by exact_mod_cast (pr Mat 0).den_pos
    have hq1 : (0:ℝ) < (pr Mat 1).den := by exact_mod_cast (pr Mat 1).den_pos
    have htp : 0 < (Mat 2:ℝ)*(pr Mat 0:ℝ)+Mat 3 := by
      linarith only [(hpt Mat hMat).1]
    have he := (div_eq_iff htp.ne').mp (hpmap Mat hMat)
    have hid : ((Mat 0:ℝ)*(pr Mat 0:ℝ)+Mat 1)/(pr Mat 0:ℝ)=
        ((pr Mat 1).num:ℝ)/(pr Mat 0).num := by
      rw [he,hpMatt Mat hMat]
      change ((pr Mat 1:ℝ)*(((pr Mat 1).den:ℝ)/(pr Mat 0).den))/(pr Mat 0:ℝ)=
        ((pr Mat 1).num:ℝ)/(pr Mat 0).num
      simp only [Rat.cast_def]
      field_simp [hq0.ne',hq1.ne',hnum0]
    rw [hid]
    have hh := abs_le.mp (hratios Mat hMat).2
    constructor <;> linarith only [hh.1,hh.2,hθmax]
  have hpointMass Mat (hMat : Mat∈Occupied) :
      (∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
        Aweight*(Kstar/|(Mat 2:ℝ)|)^((3:ℝ)⁻¹)+Bweight/|(Mat 2:ℝ)| := by
    exact matrix_sample_mass_weight_majorant (Nat.cast_nonneg m0)
      (abs_pos.mpr (by exact_mod_cast (hpcap Mat hMat).1)) (hpcap Mat hMat).2
      (hmass Mat (hin hMat))
  have hsum := resonance_matrix_curvature_band_cubic_weight_sum Occupied
    (fun Mat => (pr Mat 0:ℝ)) (fun Mat => (pr Mat 1:ℝ))
    hlambda hGcap hAweight hKstar hBweight
    (fun Mat hMat => hMatdet Mat (hin hMat)) hpcap
    (fun Mat hMat => hpcurv Mat hMat 0) (fun Mat hMat => hpcurv Mat hMat 1)
    hpt hpmap hpnum (fun Mat hMat => haction Mat (hin hMat))
  have hsumOcc : (∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ))=
      ∑ Mat∈Occupied, ∑ ab∈Gaps, ((S Mat ab).card:ℝ) := by
    symm
    apply Finset.sum_subset hin
    intro Mat hMat hnot
    apply Finset.sum_eq_zero
    intro ab hab
    have he : S Mat ab=∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      exact hnot (Finset.mem_filter.mpr ⟨hMat,ab,hab,hne⟩)
    simp only [he,Finset.card_empty,Nat.cast_zero]
  rw [hsumOcc]
  exact (Finset.sum_le_sum hpointMass).trans hsum


example
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Matrices : Finset (Fin 4 → ℤ)) (Bmajor Cmajor : ℕ)
    (S : (Fin 4 → ℤ) → ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℚ)
    (vinv : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → Fin 2)
    (anchor : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((x Mat) ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, (((rat Mat) ab) j i).den ≤ Q ∧ Q ≤ 2*(((rat Mat) ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, lambda ≤ |(((rat Mat) ab) j i:ℝ)| ∧ |(((rat Mat) ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((((rat Mat) ab) j i).den:ℤ) ∣ (((rat Mat) ab) j i).num*((vinv Mat) ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (((rat Mat) ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : ∀ Mat∈Matrices, Mat 2 ≠ 0)
    (hlarge : ∀ Mat∈Matrices, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (haction : ∀ Mat∈Matrices, 8*Uband ≤ |(Mat 2:ℝ)| *lambda^2)
    (hV : 1 ≤ V)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊((((rat Mat) ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((((rat Mat) ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((sourceColor Mat) ab) j 0=((sourceColor Mat) ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, iteratedDeriv 2 (f i) (((x Mat) ab) j i)/2=(((rat Mat) ab) j i:ℝ)) →
    let q := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (((rat Mat) ab) j i).den
    let mu := fun Mat => fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round (((x Mat) ab) j i))/6
    let ell := fun Mat => fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round (((x Mat) ab) j i))
    let b := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i⌋+(((parity Mat) ab) j i:ℕ) : ℤ)
    let cround := fun Mat => fun (ab : ℝ × ℝ) => fun j i => round ((((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)
    let tau := fun Mat => fun (ab : ℝ × ℝ) => fun j i => ((((b Mat) ab) j i:ℝ)-(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)/2
    let dual := fun Mat => fun (ab : ℝ × ℝ) => fun j i => -2*((mu Mat) ab) j i*(Real.sqrt (2/(3*((mu Mat) ab) j i*(((q Mat) ab) j i:ℝ))))^3
    let cloud := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-(((vinv Mat) ab) j i:ℝ)*((b Mat) ab) j i/((q Mat) ab) j i),
      Int.fract (-(((vinv Mat) ab) j i:ℝ)/((q Mat) ab) j i),((dual Mat) ab) j i/Real.sqrt K₀,
      (3*((dual Mat) ab) j i*((tau Mat) ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((b Mat) ab) j 0-((cround Mat) ab) j 0=((b Mat) ab) j 1-((cround Mat) ab) j 1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ a, |((cloud Mat) ab) j 0 a-((cloud Mat) ab) j 1 a| ≤ 2*radius a) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈S Mat ab,
      |cloud Mat ab j 0 1-cloud Mat ab j 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ Mat∈Matrices, Mat 0*Mat 3-Mat 1*Mat 2=1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3=(((q Mat) ab) j 1:ℝ)/((q Mat) ab) j 0) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((Mat 0:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3)=(((rat Mat) ab) j 1:ℝ)) →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), |(((anchor Mat) ab) j:ℝ)-(((rat Mat) ab) j 0:ℝ)| ≤ ε) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256*((((anchor Mat) ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*(((anchor Mat) ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Gcap := R^4/(6*N^2*V)
    let Kstar := 2*Cfirst*R^4/(Lunit^3*N^2)
    let Aweight := 4*(m0:ℝ)
    let Bweight := 4*(m0:ℝ)*Cpack*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (m0:ℝ)*Cgap*R^4/(N^2*(Uref:ℝ))+2*(m0:ℝ)*Gcap
    (∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
      588*(Uband/lambda)^2*Uband^2*Gcap*
        (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight) :=
  HuxleyMatrixSourceScratch.physicalModelPhase_actual_fourier_charted_matrix_source_mass_core Uref Refs Gaps (Bselect:=Bselect) Matrices Bmajor Cmajor S Q K₀ rat vinv parity anchor e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut) (lambda:=lambda) (Uband:=Uband) (θ:=θ) (V:=V) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap



theorem physicalModelPhase_actual_fourier_charted_matrix_source_mass
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Matrices : Finset (Fin 4 → ℤ)) (Bmajor Cmajor : ℕ)
    (S : (Fin 4 → ℤ) → ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℚ)
    (vinv : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → Fin 2)
    (anchor : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((x Mat) ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, (((rat Mat) ab) j i).den ≤ Q ∧ Q ≤ 2*(((rat Mat) ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, lambda ≤ |(((rat Mat) ab) j i:ℝ)| ∧ |(((rat Mat) ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((((rat Mat) ab) j i).den:ℤ) ∣ (((rat Mat) ab) j i).num*((vinv Mat) ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (((rat Mat) ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : ∀ Mat∈Matrices, Mat 2 ≠ 0)
    (hlarge : ∀ Mat∈Matrices, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (haction : ∀ Mat∈Matrices, 8*Uband ≤ |(Mat 2:ℝ)| *lambda^2)
    (hV : 1 ≤ V)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊((((rat Mat) ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((((rat Mat) ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((sourceColor Mat) ab) j 0=((sourceColor Mat) ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, iteratedDeriv 2 (f i) (((x Mat) ab) j i)/2=(((rat Mat) ab) j i:ℝ)) →
    let q := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (((rat Mat) ab) j i).den
    let mu := fun Mat => fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round (((x Mat) ab) j i))/6
    let ell := fun Mat => fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round (((x Mat) ab) j i))
    let b := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i⌋+(((parity Mat) ab) j i:ℕ) : ℤ)
    let cround := fun Mat => fun (ab : ℝ × ℝ) => fun j i => round ((((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)
    let tau := fun Mat => fun (ab : ℝ × ℝ) => fun j i => ((((b Mat) ab) j i:ℝ)-(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)/2
    let dual := fun Mat => fun (ab : ℝ × ℝ) => fun j i => -2*((mu Mat) ab) j i*(Real.sqrt (2/(3*((mu Mat) ab) j i*(((q Mat) ab) j i:ℝ))))^3
    let cloud := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-(((vinv Mat) ab) j i:ℝ)*((b Mat) ab) j i/((q Mat) ab) j i),
      Int.fract (-(((vinv Mat) ab) j i:ℝ)/((q Mat) ab) j i),((dual Mat) ab) j i/Real.sqrt K₀,
      (3*((dual Mat) ab) j i*((tau Mat) ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((b Mat) ab) j 0-((cround Mat) ab) j 0=((b Mat) ab) j 1-((cround Mat) ab) j 1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ a, |((cloud Mat) ab) j 0 a-((cloud Mat) ab) j 1 a| ≤ 2*radius a) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈S Mat ab,
      |cloud Mat ab j 0 1-cloud Mat ab j 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ Mat∈Matrices, Mat 0*Mat 3-Mat 1*Mat 2=1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3=(((q Mat) ab) j 1:ℝ)/((q Mat) ab) j 0) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((Mat 0:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3)=(((rat Mat) ab) j 1:ℝ)) →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), |(((anchor Mat) ab) j:ℝ)-(((rat Mat) ab) j 0:ℝ)| ≤ ε) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256*((((anchor Mat) ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*(((anchor Mat) ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Gcap := R^4/(6*N^2*V)
    let Kstar := 2*Cfirst*R^4/(Lunit^3*N^2)
    let Aweight := 4*(m0:ℝ)
    let Bweight := 4*(m0:ℝ)*Cpack*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (m0:ℝ)*Cgap*R^4/(N^2*(Uref:ℝ))+2*(m0:ℝ)*Gcap
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    ((∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
      588*(Uband/lambda)^2*Uband^2*Gcap*
        (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight)) ∧
    (∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
      588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/N^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) := by
  classical
  intro Vheight P₁ P₂ ε Ccharts sourceColor hsourceColor f hlevel
    q mu ell b cround tau dual cloud radius hcolor hnear hnearNarrow
    κ Cphys c J B hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    H hNtwo hL hU hanchor hcut hcount C₂ C₃ Ct Cc Δ
    Ccurv D Kres Esize Dbase Tbase hsize hD hΔ hBsize
    Blabels m0 hBmajor hCmajor Lunit Gamma Cthird Cpack Cfirst Cgap
    Gcap Kstar Aweight Bweight Cmain Ctail
  have hraw := physicalModelPhase_actual_fourier_charted_matrix_source_mass_core
    Uref Refs Gaps (Bselect:=Bselect) Matrices Bmajor Cmajor S Q K₀
    rat vinv parity anchor e r v s
    hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap
    hc hlarge haction hV hgap
    hsourceColor hlevel hcolor hnear hnearNarrow
    hsmall hNR hRN hNcube hminscale hMatdet hMatt hMatmap hMatgamma
    hNtwo hL hU hanchor hcut hcount hsize hD hΔ hBsize hBmajor hCmajor
  have hκ : 0 < κ := modelPhaseThirdLower_pos hσ
  have hCphys : 0 < Cphys := by dsimp only [Cphys]; positivity
  have hunit : 0 < Lunit := div_pos (mul_pos (by norm_num) hκ) hCphys
  have hUp : (0:ℝ) < Uref := by exact_mod_cast (show 0 < Uref by omega)
  have hδ0 := approximateModelPhase_tolerance_nonneg (hF 0)
  have hC₂ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 2) hδ0
  have hC₃ := add_nonneg (modelPhaseJetCoefficient_nonneg σ 3) hδ0
  obtain ⟨hCR,hCN⟩ := physical_source_quartic_constants_nonneg hσ hδ0
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  have hCc : 0 ≤ Cc := by dsimp only [Cc]; positivity
  have hK : 0 ≤ Kres := by dsimp only [Kres]; positivity
  have hΓ : 0 ≤ Gamma := div_nonneg hCphys.le hκ.le
  have hCthird : 0 ≤ Cthird :=
    mul_nonneg hΓ (add_nonneg (mul_nonneg (by norm_num) hK)
      (mul_nonneg (by norm_num) hCR))
  have hcore : 0 ≤ Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ :=
    add_nonneg (mul_nonneg (sq_nonneg Gamma) hCthird)
      (div_nonneg (mul_nonneg hΓ hC₃) hκ.le)
  have hCpack : 0 ≤ Cpack :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hcore) hκ.le
  have hCfirst : 0 ≤ Cfirst :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le) hcore) (sq_nonneg κ)
  have hCgap : 0 ≤ Cgap :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCphys.le)
      (add_nonneg (mul_nonneg (sq_nonneg Gamma) hB)
        (div_nonneg (mul_nonneg hΓ hC₃) hκ.le))) hκ.le
  refine ⟨hraw,hraw.trans ?_⟩
  exact matrix_physical_source_scale (zero_lt_one.trans_le hR) hN hunit hUp hV
    hCfirst hCpack hCgap (Nat.cast_nonneg m0)


example
    (Uref : ℕ) (Refs : Finset ℝ) (Gaps : Finset (ℝ × ℝ)) {Bselect : ℝ}
    (Matrices : Finset (Fin 4 → ℤ)) (Bmajor Cmajor : ℕ)
    (S : (Fin 4 → ℤ) → ℝ × ℝ → Finset ℕ) (Q K₀ : ℕ) [NeZero K₀]
    (rat : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℚ)
    (vinv : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℤ)
    (parity : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → Fin 2)
    (anchor : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → ℚ)
    (e r v s : ℝ × ℝ → ℤ)
    {σ δ T M N R base Bcut lambda Uband θ V : ℝ}
    {F : Fin 2 → ℝ → ℝ} {A W : Fin 2 → ℝ}
    {x : (Fin 4 → ℤ) → ℝ × ℝ → ℕ → Fin 2 → ℝ}
    (hσ : 0 < σ)
    (hδ : δ ≤ min (modelPhaseThirdLower σ) 1)
    (hF : ∀ i, Expdb.IsApproximateModelPhaseFunction (F i) σ 4 δ)
    (hT : 0 < T)
    (hM : 0 < M)
    (hN : 0 < N)
    (hR : 1 ≤ R)
    (hRM : R ≤ M)
    (hQ : 0 < Q)
    (hscale : T*N*R^2=M^3)
    (hmesh : (Q:ℝ)*N ≤ (K₀:ℝ)*R^2)
    (hA : ∀ i, M ≤ A i)
    (hW : ∀ i, A i+W i ≤ 2*M)
    (hx : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i∈Ioo (1/2:ℝ) (W i-1/2))
    (hwindow : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((x Mat) ab) j 0∈Icc (base+N*(j:ℝ)) (base+N*((j:ℝ)+1)))
    (hden : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, (((rat Mat) ab) j i).den ≤ Q ∧ Q ≤ 2*(((rat Mat) ab) j i).den)
    (hlambda : 0 < lambda)
    (hUband : 0 ≤ Uband)
    (hθ : 0 < θ)
    (hθmax : θ ≤ 1/24)
    (hcurv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, lambda ≤ |(((rat Mat) ab) j i:ℝ)| ∧ |(((rat Mat) ab) j i:ℝ)| ≤ Uband)
    (hinv : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((((rat Mat) ab) j i).den:ℤ) ∣ (((rat Mat) ab) j i).num*((vinv Mat) ab) j i-1)
    (hchart : ∀ ab∈Gaps, (v ab)*(r ab)-(e ab)*(s ab)=1)
    (horientation : ∀ ab∈Gaps, ((0:ℝ) < (r ab) ∧ ((e ab):ℝ)/(r ab)=ab.1) ∨
      (((r ab):ℝ) < 0 ∧ ((e ab):ℝ)/(r ab)=ab.2))
    (hBcut : 0 < Bcut)
    (hs : ∀ ab∈Gaps, (s ab) ≠ 0)
    (hrefSet : ∀ ab∈Gaps, ((e ab):ℝ)/(r ab)∈Refs)
    (hparentSet : ∀ ab∈Gaps, ((v ab):ℝ)/(s ab)∈Refs)
    (hsep : ∀ a∈Refs, ∀ b∈Refs, a ≠ b → ((Uref:ℝ)/R^2)/4 < |a-b|)
    (hwideL : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hwideU : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+(56*(Uref:ℝ)/modelPhaseThirdLower σ)*N∈Ioo (1/2:ℝ) (W i-1/2))
    (hUref : 1 ≤ Uref)
    (hBselectSize : 2+168/modelPhaseThirdLower σ ≤ Bselect)
    (hcutMargin : 7*Bcut ≤ modelPhaseThirdLower σ*Bselect)
    (hselectedWrap : Bselect^2*(Uref:ℝ)^3*R^2 ≤ N^2)
    (hreferenceDen : ∀ ab∈Gaps, R^2 ≤ ((r ab):ℝ)^2*(Uref:ℝ))
    (hgapWidth : ∀ ab∈Gaps, ab.2-ab.1 ≤ 7*(Uref:ℝ)/(2*R^2))
    (hRQ : R ≤ (Q:ℝ))
    (hselectedUpper : (Uref:ℝ) ≤ (N/(Q:ℝ))^((2:ℝ)/3)/Bselect)
    (hscaleTen : N^10 ≤ M^3*R^7)
    (hfamilyGap : ∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (((rat Mat) ab) j 0:ℝ)∈Icc ab.1 ab.2)
    (hc : ∀ Mat∈Matrices, Mat 2 ≠ 0)
    (hlarge : ∀ Mat∈Matrices, 64*(modelPhaseJetCoefficient σ 3+δ)*M^2 ≤
      |(Mat 2:ℝ)| *(modelPhaseThirdLower σ)^2*T)
    (haction : ∀ Mat∈Matrices, 8*Uband ≤ |(Mat 2:ℝ)| *lambda^2)
    (hV : 1 ≤ V)
    (hgap : ∀ ab∈Gaps, ab.1∈Refs ∧ ab.2∈Refs ∧ ab.1 < ab.2 ∧
      ∀ t∈Refs, ¬(ab.1 < t ∧ t < ab.2)) :
    let Vheight := T*(modelPhaseJetCoefficient σ 1+δ)/(2*M^2)
    let P₁ := fun (ab : ℝ × ℝ) => 1+(|((v ab):ℝ)|+|((s ab):ℝ)| *Vheight)*(Q:ℝ)
    let P₂ := fun (ab : ℝ × ℝ) => 1+(|((r ab):ℝ)| *Vheight+|((e ab):ℝ)|)*(Q:ℝ)
    let ε := modelPhaseThirdLower σ/(16*(σ*(σ+1)+1+2)*R^2)
    let Ccharts := fun (ab : ℝ × ℝ) => ⌊Real.logb (5/4) ((ab.2-ab.1)/(12*ε))⌋₊+1
    let sourceColor := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊((((rat Mat) ab) j i).den:ℝ)/(θ*((Q:ℝ)/2))⌋,
      ⌊((((rat Mat) ab) j i).num:ℝ)/(θ*(lambda*(Q:ℝ)/2))⌋)
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((sourceColor Mat) ab) j 0=((sourceColor Mat) ab) j 1) →
    let f := fun i => heathBrownPhysicalPhase (F i) T M (A i) 1
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, iteratedDeriv 2 (f i) (((x Mat) ab) j i)/2=(((rat Mat) ab) j i:ℝ)) →
    let q := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (((rat Mat) ab) j i).den
    let mu := fun Mat => fun (ab : ℝ × ℝ) => fun j i => iteratedDeriv 3 (f i) (round (((x Mat) ab) j i))/6
    let ell := fun Mat => fun (ab : ℝ × ℝ) => fun j i => deriv (f i) (round (((x Mat) ab) j i))
    let b := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (⌊(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i⌋+(((parity Mat) ab) j i:ℕ) : ℤ)
    let cround := fun Mat => fun (ab : ℝ × ℝ) => fun j i => round ((((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)
    let tau := fun Mat => fun (ab : ℝ × ℝ) => fun j i => ((((b Mat) ab) j i:ℝ)-(((q Mat) ab) j i:ℝ)*((ell Mat) ab) j i)/2
    let dual := fun Mat => fun (ab : ℝ × ℝ) => fun j i => -2*((mu Mat) ab) j i*(Real.sqrt (2/(3*((mu Mat) ab) j i*(((q Mat) ab) j i:ℝ))))^3
    let cloud := fun Mat => fun (ab : ℝ × ℝ) => fun j i => (![Int.fract (-(((vinv Mat) ab) j i:ℝ)*((b Mat) ab) j i/((q Mat) ab) j i),
      Int.fract (-(((vinv Mat) ab) j i:ℝ)/((q Mat) ab) j i),((dual Mat) ab) j i/Real.sqrt K₀,
      (3*((dual Mat) ab) j i*((tau Mat) ab) j i/2)/Real.sqrt K₀] : Fin 4 → ℝ)
    let radius : Fin 4 → ℝ := ![1/(12*(K₀:ℝ)),1/(12*(K₀:ℝ)^2),(1/(K₀:ℝ)^2)/12,(1/(K₀:ℝ))/12]
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((b Mat) ab) j 0-((cround Mat) ab) j 0=((b Mat) ab) j 1-((cround Mat) ab) j 1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ a, |((cloud Mat) ab) j 0 a-((cloud Mat) ab) j 1 a| ≤ 2*radius a) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈S Mat ab,
      |cloud Mat ab j 0 1-cloud Mat ab j 1 1| ≤ 1/(6*(K₀:ℝ)^2*V)) →
    let κ := modelPhaseThirdLower σ
    let Cphys := σ*(σ+1)+1
    let c := κ/6
    let J := Cphys/6
    let B := max 1 (max (2*Real.sqrt J) (8*J*Real.sqrt J/(3*c)))
    B*R^2/N^2 ≤ 1/2 →
    N ≤ R^2 →
    R ≤ N →
    N^3 ≤ M*R^2 →
    2*R^2 ≤ (Q:ℝ)*N →
    (∀ Mat∈Matrices, Mat 0*Mat 3-Mat 1*Mat 2=1) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), (Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3=(((q Mat) ab) j 1:ℝ)/((q Mat) ab) j 0) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ((Mat 0:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 1)/
      ((Mat 2:ℝ)*(((rat Mat) ab) j 0:ℝ)+Mat 3)=(((rat Mat) ab) j 1:ℝ)) →
    (∀ Mat∈Matrices, |(Mat 2:ℝ)| ≤ (Q:ℝ)^2/(6*(K₀:ℝ)^2)) →
    let H := N/(Cphys+2)
    2 ≤ N →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i-H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), ∀ i, ((x Mat) ab) j i+H∈Ioo (1/2:ℝ) (W i-1/2)) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), |(((anchor Mat) ab) j:ℝ)-(((rat Mat) ab) j 0:ℝ)| ≤ ε) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256*((((anchor Mat) ab) j).den:ℝ) ≤ (Q:ℝ)/3) →
    (∀ Mat∈Matrices, ∀ ab∈Gaps, ∀ j∈((S Mat) ab), 256 ≤ (2*ε)*((Q:ℝ)/3)*(((anchor Mat) ab) j).den) →
    let C₂ := modelPhaseJetCoefficient σ 2+δ
    let C₃ := modelPhaseJetCoefficient σ 3+δ
    let Ct := C₂/2+5*C₃/12
    let Cc := C₂/κ+C₃/(2*κ)
    let Δ := (37*B/2+16*B*Cc+2*Ct+2*Cc)*(Q:ℝ)/N
    let Ccurv := (4/κ)*(B+2*quarticReciprocalConstant σ δ)
    let D := Δ+quarticNonlinearResidualConstant σ δ*(2*(Q:ℝ))/N
    let Kres := 4*(37*B/2+16*B*Cc+2*Ct+2*Cc+
      2*quarticNonlinearResidualConstant σ δ)/κ
    let Esize := κ/(16*(Cphys+2))
    let Dbase := 37*B/2+16*B*Cc+2*Ct+2*Cc+2*quarticNonlinearResidualConstant σ δ
    let Tbase := (2/κ)*(B+2*quarticReciprocalConstant σ δ)
    2*3840*128^2*105*(Dbase+64*Tbase*Esize^2) ≤ Bselect*Esize →
    D ≤ 1/2 → Δ < 1/2 → 61*Ccurv*Cphys ≤ Bcut →
    let Blabels := fun ab => 6+216*(⌊Real.logb 2 (P₁ ab*P₂ ab)⌋₊+1)
    let m0 := 6+Cmajor*(105+544*Bmajor)
    (∀ ab∈Gaps, Blabels ab ≤ Bmajor) →
    (∀ ab∈Gaps, Ccharts ab ≤ Cmajor) →
    let Lunit := 2*κ/Cphys
    let Gamma := Cphys/κ
    let Cthird := Gamma*(32*Kres+9*quarticReciprocalConstant σ δ)
    let Cpack := 64*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Cfirst := 128*Cphys*(Gamma^2*Cthird+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ^2
    let Cgap := 64*Cphys*(Gamma^2*B+Gamma*(modelPhaseJetCoefficient σ 3+δ)/κ)/κ
    let Gcap := R^4/(6*N^2*V)
    let Kstar := 2*Cfirst*R^4/(Lunit^3*N^2)
    let Aweight := 4*(m0:ℝ)
    let Bweight := 4*(m0:ℝ)*Cpack*R^4/(Lunit^2*N^2*(Uref:ℝ))+
      (m0:ℝ)*Cgap*R^4/(N^2*(Uref:ℝ))+2*(m0:ℝ)*Gcap
    let Cmain := 4*(2*Cfirst/Lunit^3)^((3:ℝ)⁻¹)+2
    let Ctail := 4*Cpack/Lunit^2+Cgap
    ((∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
      588*(Uband/lambda)^2*Uband^2*Gcap*
        (Aweight*Kstar^((3:ℝ)⁻¹)*Gcap^((2:ℝ)/3)+Bweight)) ∧
    (∑ Mat∈Matrices, ∑ ab∈Gaps, ((S Mat ab).card:ℝ)) ≤
      588*(m0:ℝ)*(Uband/lambda)^2*Uband^2*(R^8/N^4)*
        (Cmain/V^((5:ℝ)/3)+Ctail/((Uref:ℝ)*V)) :=
  HuxleyMatrixSourceScratch.physicalModelPhase_actual_fourier_charted_matrix_source_mass Uref Refs Gaps (Bselect:=Bselect) Matrices Bmajor Cmajor S Q K₀ rat vinv parity anchor e r v s (σ:=σ) (δ:=δ) (T:=T) (M:=M) (N:=N) (R:=R) (base:=base) (Bcut:=Bcut) (lambda:=lambda) (Uband:=Uband) (θ:=θ) (V:=V) (F:=F) (A:=A) (W:=W) (x:=x) hσ hδ hF hT hM hN hR hRM hQ hscale hmesh hA hW hx hwindow hden hlambda hUband hθ hθmax hcurv hinv hchart horientation hBcut hs hrefSet hparentSet hsep hwideL hwideU hUref hBselectSize hcutMargin hselectedWrap hreferenceDen hgapWidth hRQ hselectedUpper hscaleTen hfamilyGap hc hlarge haction hV hgap



#print axioms cubic_matrix_source_scale
#print axioms matrix_physical_source_scale
#print axioms physicalModelPhase_actual_fourier_charted_matrix_source_mass_core

#print axioms physical_source_quartic_constants_nonneg
#print axioms mobius_upper_right_large_action_comparison
#print axioms mobius_reciprocal_entry_bounds
#print axioms resonance_matrix_reciprocal_sum
#print axioms cubic_reciprocal_majorant
#print axioms resonance_matrix_cubic_weight_sum
#print axioms resonance_matrix_reciprocal_cubic_weight_sum
#print axioms resonance_matrix_curvature_band_cubic_weight_sum
#print axioms matrix_sample_mass_weight_majorant
#print axioms physicalModelPhase_actual_fourier_charted_matrix_source_mass
end HuxleyMatrixSourceScratch
