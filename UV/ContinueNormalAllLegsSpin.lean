import UV.ContinueNormalHolonomyCoefficient
import UV.ContinueWilsonSpinRotation
import UV.FurtherOpticalProjector
import UV.RadialAveraging

/-! The zero-transfer spin trace of the affine transverse vertex in the
three-compression comparison. The fifth frequency is spacelike and every
polarization is a unit vector of the carrier four-plane. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure UV.SectorPlane
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

namespace UV

theorem normal_five_slash_traceless (p : OSFourSpace) (ξ : ℝ) : (normalFiveSlash p ξ).trace = 0 := by
  let U := diracSlash (osAxis 0).val
  let J := normalCoverGamma5
  have hu : U*U = 1 := by simpa only [U,(osAxis 0).property,one_pow,Complex.ofReal_one,one_smul] using diracSlash_sq (osAxis 0).val
  have ha : J*U = -(U*J) := normal_chirality_anticommutes _
  have h1 : (U*J*U).trace = J.trace := by rw [Matrix.trace_mul_comm (U*J) U,←mul_assoc,hu,one_mul]
  have h2 : U*J*U = -J := by rw [mul_assoc,ha,mul_neg,←mul_assoc,hu,one_mul]
  rw [h2,Matrix.trace_neg] at h1
  have hJ : J.trace = 0 := by linear_combination (-1/2:ℂ)*h1
  change (diracSlash p+(ξ:ℂ) • J).trace = 0
  simp only [Matrix.trace_add,Matrix.trace_smul,FurtherOptical.slash_trace_zero,hJ,smul_zero,add_zero]

/-- The spin trace with the scalar form factors and the two factors i
stripped from the vertices. The carrier polarization may be any unit vector. -/
theorem normal_zero_transfer_spin (m : ℝ) (p : OSFourSpace) (ξ : ℝ) (u : UnitVector OSFourSpace) :
    ((normalDiracFrequency m p ξ*diracSlash u.val)*(normalDiracFrequency m p ξ*diracSlash u.val)).trace =
      ((4 * (normalFiveDenom m p ξ - 2*⟪u.val,p⟫^2) / normalFiveDenom m p ξ^2 : ℝ):ℂ) := by
  let P := normalFiveSlash p ξ
  let U := diracSlash u.val
  let B := P*U
  let c : ℂ := (⟪u.val,p⟫:ℝ)
  let s : ℂ := ((‖p‖^2+ξ^2:ℝ):ℂ)
  let d : ℂ := (normalFiveDenom m p ξ:ℝ)
  have hu : U*U=1 := by simpa only [U,u.property,one_pow,Complex.ofReal_one,one_smul] using diracSlash_sq u.val
  have hp : P*P=s • 1 := normal_five_slash_square p ξ
  have ha : U*P+P*U = (2*c) • 1 := by
    have h := wilson_slash_anticommutator u.val p
    simp only [P,U,normalFiveSlash,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,normal_chirality_anticommutes,smul_neg]
    simp only [Complex.ofReal_mul,Complex.ofReal_ofNat] at h
    linear_combination (norm := abel) h
  have hB : B.trace = 4*c := by
    have h := congrArg Matrix.trace ha
    rw [Matrix.trace_add,Matrix.trace_mul_comm U P,Matrix.trace_smul,Matrix.trace_one] at h
    change (P*U).trace = _
    norm_num [smul_eq_mul] at h
    linear_combination (1/2:ℂ)*h
  have hBB : B*B = (2*c) • B - s • 1 := by
    have h := eq_sub_of_add_eq ha
    change (P*U)*(P*U) = _
    calc (P*U)*(P*U) = (P*(U*P))*U := by noncomm_ring
         _ = (2*c) • (P*U) - (P*P)*(U*U) := by
           rw [h,mul_sub,sub_mul,mul_smul_comm,mul_one,smul_mul_assoc]
           congr 1; noncomm_ring
         _ = _ := by rw [hp,hu,mul_one]
  have hBU : B*U=P := by dsimp only [B]; rw [mul_assoc,hu,mul_one]
  have hUB : (U*B).trace = 0 := by rw [Matrix.trace_mul_comm,hBU]; exact normal_five_slash_traceless p ξ
  have hF : normalDiracFrequency m p ξ*U = d⁻¹ • ((m:ℂ) • U+(-Complex.I) • B) := by
    dsimp only [d,B,P,normalFiveSlash,normalDiracFrequency,freeDiracNumerator]
    simp only [add_mul,smul_mul_assoc,one_mul,smul_add,smul_smul]
    module
  change ((normalDiracFrequency m p ξ*U)*(normalDiracFrequency m p ξ*U)).trace = _
  have ht : P.trace = 0 := normal_five_slash_traceless p ξ
  rw [hF]
  simp only [smul_mul_smul,add_mul,mul_add,hu,hBU,hUB,hBB,Matrix.trace_smul,Matrix.trace_add,Matrix.trace_sub,Matrix.trace_one,
    ht,hB,smul_eq_mul,neg_mul_neg,Complex.I_mul_I]
  dsimp only [P,c,s,d,normalFiveDenom]
  push_cast
  norm_num
  simp only [div_eq_mul_inv,←inv_pow]
  ring

/-- Each of the two affine vertices contributes i f². -/
theorem normal_zero_transfer_hessian (m : ℝ) (p : OSFourSpace) (ξ f : ℝ) (u : UnitVector OSFourSpace) :
    let S := normalDiracFrequency m p ξ
    let V := (Complex.I*(f:ℂ)^2) • diracSlash u.val
    ((S*V)*(S*V)).trace.re = -(4*f^4*(normalFiveDenom m p ξ-2*⟪u.val,p⟫^2)/normalFiveDenom m p ξ^2) := by
  dsimp only
  rw [mul_smul_comm,smul_mul_smul,Matrix.trace_smul,normal_zero_transfer_spin]
  simp only [smul_eq_mul]
  have hi : (Complex.I*(f:ℂ)^2)*(Complex.I*(f:ℂ)^2) = -((f^4:ℝ):ℂ) := by
    push_cast
    calc _ = (Complex.I*Complex.I)*(f:ℂ)^4 := by ring
         _ = _ := by rw [Complex.I_mul_I,neg_one_mul]
  rw [hi,←Complex.ofReal_neg,←Complex.ofReal_mul,Complex.ofReal_re]
  ring

/-- Four-dimensional carrier rotations give the factor one half in the
averaged numerator, for each fixed normal frequency. The radial weight
can include the fourth power of the charged form factor and denominator. -/
theorem normal_zero_transfer_radial (m ξ : ℝ) (i : Fin 4) {g : ℝ → ℝ} (hg : Measurable g)
    (h0 : Integrable (fun p : OSFourSpace => g (‖p‖^2))) (h2 : Integrable (fun p : OSFourSpace => ‖p‖^2*g (‖p‖^2))) :
    (∫ p : OSFourSpace, -(4*(normalFiveDenom m p ξ-2*(p i)^2)*g (‖p‖^2))) =
      -(∫ p : OSFourSpace, 4*(m^2+ξ^2+‖p‖^2/2)*g (‖p‖^2)) := by
  let C := m^2+ξ^2
  let w := fun p : OSFourSpace => g (‖p‖^2)
  let q := fun p : OSFourSpace => ‖p‖^2*g (‖p‖^2)
  let b := fun p : OSFourSpace => p i*p i*g (‖p‖^2)
  have hb := radial_coordinate_product_integrable hg h2 i i
  have he (p : OSFourSpace) : -(4*(normalFiveDenom m p ξ-2*(p i)^2)*g (‖p‖^2)) =
      -4*(C*w p+q p-2*b p) := by dsimp [C,w,q,b,normalFiveDenom]; ring
  have he' (p : OSFourSpace) : 4*(m^2+ξ^2+‖p‖^2/2)*g (‖p‖^2) = 4*(C*w p+(1/2)*q p) := by dsimp [C,w,q]; ring
  simp_rw [he,he']
  have hw : Integrable w := h0
  have hq : Integrable q := h2
  have hbi : Integrable b := hb
  have hsum : Integrable (fun p => C*w p+q p) := (hw.const_mul C).add hq
  rw [integral_const_mul,integral_const_mul,integral_sub hsum (hbi.const_mul 2),
    integral_add (hw.const_mul C) hq,integral_add (hw.const_mul C) (hq.const_mul _),
    integral_const_mul,integral_const_mul,integral_const_mul]
  have hh : (∫ p, b p) = (1/4)*(∫ p, q p) := radial_coordinate_diagonal_integral hg h2 i
  rw [hh]
  ring

theorem normal_zero_transfer_negative {m : ℝ} (hm : 0 < m) (ξ : ℝ) (i : Fin 4) {g : ℝ → ℝ} (hg : Measurable g)
    (h0 : Integrable (fun p : OSFourSpace => g (‖p‖^2))) (h2 : Integrable (fun p : OSFourSpace => ‖p‖^2*g (‖p‖^2)))
    (hn : ∀ p : OSFourSpace, 0 ≤ g (‖p‖^2)) (hs : 0 < volume (Function.support (fun p : OSFourSpace => g (‖p‖^2)))) :
    (∫ p : OSFourSpace, -(4*(normalFiveDenom m p ξ-2*(p i)^2)*g (‖p‖^2))) < 0 := by
  rw [normal_zero_transfer_radial m ξ i hg h0 h2,neg_lt_zero]
  let F := fun p : OSFourSpace => 4*(m^2+ξ^2+‖p‖^2/2)*g (‖p‖^2)
  have hc (p : OSFourSpace) : 0 < 4*(m^2+ξ^2+‖p‖^2/2) := by positivity
  have hf : Integrable F := by
    have h := ((h0.const_mul (m^2+ξ^2)).add (h2.const_mul (1/2:ℝ))).const_mul 4
    apply h.congr (Filter.Eventually.of_forall fun p => ?_)
    dsimp [F]; ring
  apply (integral_pos_iff_support_of_nonneg (f := F) (fun p => mul_nonneg (hc p).le (hn p)) hf).mpr
  apply hs.trans_le (measure_mono fun p hp => ?_)
  exact mul_ne_zero (hc p).ne' hp

end UV
