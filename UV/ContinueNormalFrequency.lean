import UV.ContinueNormalCoverFourier

/-! The five-component Euclidean Clifford symbol of the normal-circle
comparison. The fifth frequency is the Fourier variable of the normal
circle. The carrier momentum lives on the selected Euclidean four-plane. -/

noncomputable section

open UV.SectorPlane
open scoped Matrix Matrix.Norms.L2Operator

namespace UV

private def gammaWord (l : List (Fin 4)) := (l.map euclideanGamma).prod

private def gammaSwapSign (j : Fin 4) (l : List (Fin 4)) : ℂ :=
  (l.map (fun i => if i = j then (1:ℂ) else -1)).prod

private theorem gamma_slide (j : Fin 4) (l : List (Fin 4)) :
    gammaWord l * euclideanGamma j = gammaSwapSign j l • (euclideanGamma j * gammaWord l) := by
  induction l with
  | nil => simp [gammaWord,gammaSwapSign]
  | cons i l ih =>
    have h (i : Fin 4) : euclideanGamma i*euclideanGamma j =
        (if i=j then (1:ℂ) else -1) • (euclideanGamma j*euclideanGamma i) := by
      by_cases he : i=j
      · simp [he]
      · simpa only [if_neg he,neg_one_smul] using
          eq_neg_of_add_eq_zero_left (by simpa only [if_neg he] using euclideanGamma_clifford i j)
    change (euclideanGamma i*gammaWord l)*euclideanGamma j = (((if i=j then (1:ℂ) else -1)*gammaSwapSign j l)) •
      (euclideanGamma j*(euclideanGamma i*gammaWord l))
    rw [mul_assoc,ih,mul_smul_comm,←mul_assoc,h,smul_mul_assoc,mul_assoc,smul_smul,mul_comm (gammaSwapSign j l)]

private def gammaReverseSign : List (Fin 4) → ℂ
  | [] => 1
  | j :: l => gammaReverseSign l * gammaSwapSign j l

private theorem gamma_reverse (l : List (Fin 4)) : (gammaWord l)ᴴ = gammaReverseSign l • gammaWord l := by
  induction l with
  | nil => simp [gammaWord,gammaReverseSign]
  | cons j l ih =>
    change (euclideanGamma j*gammaWord l)ᴴ = (gammaReverseSign l*gammaSwapSign j l) • (euclideanGamma j*gammaWord l)
    rw [Matrix.conjTranspose_mul,euclideanGamma_isHermitian j,ih,smul_mul_assoc,gamma_slide,smul_smul]

private theorem normal_gamma_word : normalCoverGamma5 = gammaWord [0,1,2,3] := by
  simp [normalCoverGamma5,gammaWord,mul_assoc]

theorem normal_chirality_hermitian : normalCoverGamma5ᴴ = normalCoverGamma5 := by
  rw [normal_gamma_word,gamma_reverse]
  have h : gammaReverseSign [0,1,2,3] = 1 := by
    norm_num [gammaReverseSign,gammaSwapSign,show (1:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide]
  rw [h,one_smul]

theorem normal_chirality_square : normalCoverGamma5*normalCoverGamma5 = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp normal_cover_gamma_unitary
  change normalCoverGamma5ᴴ * normalCoverGamma5 = 1 at h
  rwa [normal_chirality_hermitian] at h

theorem normal_chirality_anticommutes (p : OSFourSpace) :
    normalCoverGamma5*diracSlash p = -(diracSlash p*normalCoverGamma5) := by
  have hg (j : Fin 4) : normalCoverGamma5*euclideanGamma j = -(euclideanGamma j*normalCoverGamma5) := by
    rw [normal_gamma_word,gamma_slide]
    have h : gammaSwapSign j [0,1,2,3] = -1 := by
      fin_cases j <;> simp (config := { failIfUnchanged := false }) only [gammaSwapSign,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil]
      all_goals norm_num (config := { decide := true })
    rw [h,neg_one_smul]
  simp only [diracSlash,Finset.mul_sum,Finset.sum_mul,smul_mul_assoc,mul_smul_comm,hg,smul_neg,Finset.sum_neg_distrib]

def normalFiveSlash (p : OSFourSpace) (ξ : ℝ) : DiracMatrix := diracSlash p + (ξ:ℂ) • normalCoverGamma5

theorem normal_five_slash_square (p : OSFourSpace) (ξ : ℝ) :
    normalFiveSlash p ξ * normalFiveSlash p ξ = ((‖p‖^2+ξ^2 : ℝ):ℂ) • (1:DiracMatrix) := by
  simp only [normalFiveSlash,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,diracSlash_sq,
    normal_chirality_anticommutes,normal_chirality_square,smul_neg,Complex.ofReal_add]
  push_cast
  module

def normalFiveDenom (m : ℝ) (p : OSFourSpace) (ξ : ℝ) := m^2+‖p‖^2+ξ^2

/-- The exact angular-frequency multiplier found by Fourier transformation
of the oriented cover kernel. -/
def normalDiracFrequency (m : ℝ) (p : OSFourSpace) (ξ : ℝ) : DiracMatrix :=
  ((normalFiveDenom m p ξ : ℝ):ℂ)⁻¹ • (freeDiracNumerator m p + (-Complex.I*(ξ:ℂ)) • normalCoverGamma5)

theorem normal_dirac_frequency_norm {m : ℝ} (hm : 0 < m) (p : OSFourSpace) (ξ : ℝ) :
    ‖normalDiracFrequency m p ξ‖ = (Real.sqrt (normalFiveDenom m p ξ))⁻¹ := by
  let A := normalFiveSlash p ξ
  let N := (m:ℂ) • (1:DiracMatrix) + (-Complex.I) • A
  have hA : Aᴴ = A := by simp [A,normalFiveSlash,wilson_slash_hermitian,normal_chirality_hermitian]
  have hN : Nᴴ*N = ((normalFiveDenom m p ξ:ℝ):ℂ) • (1:DiracMatrix) := by
    simp only [N,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,Matrix.conjTranspose_one,
      Complex.star_def,Complex.conj_ofReal,map_neg,Complex.conj_I,neg_neg,hA,
      add_mul,mul_add,smul_mul_smul,one_mul,mul_one,Complex.I_mul_I, mul_neg,neg_neg,
      A,normal_five_slash_square,smul_smul,normalFiveDenom,Complex.ofReal_add,Complex.ofReal_pow]
    module
  have hD : 0 < normalFiveDenom m p ξ := by unfold normalFiveDenom; positivity
  have hn := Matrix.l2_opNorm_conjTranspose_mul_self N
  rw [hN,norm_smul,norm_one,mul_one,Complex.norm_real,Real.norm_of_nonneg hD.le] at hn
  have hsq := Real.sq_sqrt hD.le
  have hnorm : ‖N‖ = Real.sqrt (normalFiveDenom m p ξ) := by nlinarith [norm_nonneg N,Real.sqrt_nonneg (normalFiveDenom m p ξ)]
  have he : freeDiracNumerator m p + (-Complex.I*(ξ:ℂ)) • normalCoverGamma5 = N := by
    simp only [N,A,normalFiveSlash,freeDiracNumerator,smul_add,smul_smul]; abel
  rw [normalDiracFrequency,he,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hD.le,hnorm]
  field_simp [hD.ne',(Real.sqrt_pos.mpr hD).ne']
  nlinarith

theorem normal_frequency_is_cover_transform {m : ℝ} (hm : 0 < m) (p : OSFourSpace) (ξ : ℝ) :
    (∫ d : ℝ, Complex.exp (-Complex.I*(ξ:ℂ)*d) • normalDiracCover normalCoverGamma5 m p d) = normalDiracFrequency m p ξ := by
  simpa only [normalDiracFrequency,normalCoverEnergy,Real.sq_sqrt (show 0 ≤ m^2+‖p‖^2 by positivity),normalFiveDenom]
    using (normal_cover_angular_fourier normalCoverGamma5 hm p ξ).2

end UV
