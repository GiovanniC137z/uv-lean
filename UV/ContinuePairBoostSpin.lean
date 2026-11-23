import UV.ContinuePairBoostMass
import UV.ContinueHeatMaxwellNativeTrace

/-! Scalar spectral projection of the actual occupied and empty
Dirac bands before any moving-frame integration. -/

noncomputable section
open Matrix MeasureTheory Set Real
open scoped ENNReal RealInnerProductSpace BigOperators Matrix
namespace UV.PairCurvature

open UV.FurtherOptical UV.HeatMaxwell

private theorem spin_projector_diagonal (v w : DiracMomentum)
    (U : DiracMatrix) (hU : U*U=1) :
    (((1-projector v)*U)*(projector w*U)).trace =
      1-(diracSlash v*U*(diracSlash w*U)).trace/4 := by
  let V := diracSlash v
  let W := diracSlash w
  have h₁ : (1-projector v)*U = (1/2:ℂ) • (U+V*U) := by
    dsimp [projector,V]
    rw [sub_mul,smul_mul_assoc,sub_mul,one_mul]
    module
  have h₂ : projector w*U = (1/2:ℂ) • (U-W*U) := by
    rw [projector,smul_mul_assoc,sub_mul,one_mul]
  have h₃ : (U*(W*U)).trace=0 := by
    rw [trace_mul_comm U, mul_assoc, hU, mul_one]
    exact slash_trace_zero w
  have h₄ : (V*U*U).trace=0 := by
    rw [mul_assoc,hU,mul_one]
    exact slash_trace_zero v
  rw [h₁,h₂,smul_mul_smul,trace_smul,add_mul,mul_sub,mul_sub,
    trace_add,trace_sub,trace_sub,hU,h₃,h₄]
  norm_num [trace_one,smul_eq_mul,V,W]
  ring

private theorem currentBlock_diag_trace {m : ℝ} (hm : 0 < m)
    (P k : ChargeSpatialMomentum) (i : Fin 4) :
    chargeInclusiveSquare (currentBlock m P k i) =
      (((1-projector (coefficients m 0 k))*currentGamma i)*
        (projector (coefficients m 0 (k-P))*currentGamma i)).trace.re := by
  let v := coefficients m 0 k
  let w := coefficients m 0 (k-P)
  let A := 1-projector v
  let B := projector w
  let U := currentGamma i
  have hA : Aᴴ=A := by simp [A,conjTranspose_sub,projector_adjoint]
  have hB : Bᴴ=B := projector_adjoint w
  have hU : Uᴴ=U := by unfold U currentGamma; split_ifs <;> simp [slash_adjoint]
  have hAA : A*A=A := by
    dsimp [A]
    rw [sub_mul,mul_sub,mul_sub,one_mul,one_mul,mul_one,
      projector_idempotent _ (coefficients_norm_sq hm le_rfl k),sub_self,sub_zero]
  have hBB : B*B=B := projector_idempotent _ (coefficients_norm_sq hm le_rfl _)
  rw [chargeInclusiveSquare_eq_trace]
  change (((A*U*B)ᴴ)*(A*U*B)).trace.re = ((A*U)*(B*U)).trace.re
  simp only [conjTranspose_mul,hA,hB,hU]
  congr 1
  calc
    _ = (((B*U)*(A*A)*U)*B).trace := by congr 1; noncomm_ring
    _ = ((B*B)*(U*(A*U))).trace := by
      rw [hAA,trace_mul_comm _ B]
      congr 1
      noncomm_ring
    _ = _ := by rw [hBB,← mul_assoc B,trace_mul_comm (B*U)]

def contractedPairSpin (m : ℝ) (P k : ChargeSpatialMomentum) :=
  ((∑ i : Fin 3, chargeInclusiveSquare (currentBlock m P k i.succ)) -
    chargeInclusiveSquare (currentBlock m P k 0))/3

private theorem pair_coeff_zero {m : ℝ} (hm : 0 < m) (k : ChargeSpatialMomentum) :
    coefficients m 0 k 0 = m/energy m k := by
  change diagonal m 0 k/energy m k = _
  simp [FurtherOptical.diagonal,attenuation,energy_sq,sqrt_sq hm.le]

private theorem pair_coeff_succ (m : ℝ) (k : ChargeSpatialMomentum) (j : Fin 3) :
    coefficients m 0 k j.succ = k j/energy m k := by
  change attenuation 0 k*k j/energy m k = _
  simp [attenuation]

/-- The transverse scalar contraction of the moving spin sum has exactly
the on-shell invariant factor s+2m², with the original constituent
energy factors. This uses the time component with its Lorentzian sign. -/
theorem contracted_pair_spin {m : ℝ} (hm : 0 < m) (P k : ChargeSpatialMomentum) :
    contractedPairSpin m P k =
      (invariantMassSq m P k+2*m^2)/(3*energy m k*energy m (P-k)) := by
  let v := coefficients m 0 k
  let w := coefficients m 0 (k-P)
  have h₀ : chargeInclusiveSquare (currentBlock m P k 0) = 1-⟪v,w⟫ := by
    rw [currentBlock_diag_trace hm,currentGamma,if_pos rfl,spin_projector_diagonal _ _ _ (one_mul _)]
    simp only [mul_one,heat_slash_pair,Complex.sub_re,Complex.one_re,Complex.div_ofNat_re,Complex.ofReal_re,v,w]
    ring
  have h₁ (i : Fin 3) : chargeInclusiveSquare (currentBlock m P k i.succ) =
      1+⟪v,w⟫-2*v i.succ*w i.succ := by
    rw [currentBlock_diag_trace hm,currentGamma,if_neg (Fin.succ_ne_zero _)]
    let u := osAxis i.succ
    have hu : diracSlash u.val*diracSlash u.val=1 := by
      simp [diracSlash_sq,u.property]
    rw [spin_projector_diagonal _ _ _ hu,heat_slash_quad]
    have hv (z : DiracMomentum) : ⟪z,u.val⟫ = z i.succ := by
      simp [u,osAxis,EuclideanSpace.inner_single_right]
    rw [hv,hv,u.property]
    simp only [one_pow,mul_one,Complex.sub_re,Complex.one_re,Complex.div_ofNat_re,Complex.ofReal_re,v,w]
    ring
  have hb : energy m (k-P) = energy m (P-k) := by unfold energy; rw [norm_sub_rev]
  let E := energy m k
  let F := energy m (P-k)
  have hE : 0 < E := energy_pos hm _
  have hF : 0 < F := energy_pos hm _
  have hsum : (∑ i : Fin 3, v i.succ*w i.succ) = ⟪k,k-P⟫/(E*F) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
    change (∑ i : Fin 3, v i.succ*w i.succ) = (∑ i : Fin 3, (k-P) i*k i)/(E*F)
    simp only [v,w,pair_coeff_succ,hb,div_mul_div_comm,← Finset.sum_div,E,F,mul_comm]
  have hinner : ⟪v,w⟫ = m^2/(E*F) + ⟪k,k-P⟫/(E*F) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
    change (∑ i : Fin 4, w i*v i) = _
    rw [Fin.sum_univ_succ,show (∑ i : Fin 3, w i.succ*v i.succ) = _ from
      (Finset.sum_congr rfl (fun i _ => mul_comm (w i.succ) (v i.succ))).trans hsum]
    simp only [v,w,pair_coeff_zero hm,hb,div_mul_div_comm,E,F]
    ring
  have hs : invariantMassSq m P k = 2*m^2+2*E*F+2*⟪k,k-P⟫ := by
    unfold invariantMassSq relativeEnergy
    change (E+F)^2-‖P‖^2=_
    have he := energy_sq m k
    have hf := energy_sq m (P-k)
    have hn := norm_sub_sq_real P k
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm k P] at hn
    change E^2 = _ at he
    change F^2 = _ at hf
    linarith [show (E+F)^2=E^2+F^2+2*E*F by ring]
  unfold contractedPairSpin
  simp_rw [h₀,h₁]
  rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  simp_rw [mul_assoc (2:ℝ)]
  rw [← Finset.mul_sum,hsum,hinner,hs]
  change _ = _/(3*E*F)
  norm_num [nsmul_eq_mul]
  field_simp [hE.ne',hF.ne']
  ring

/-- The scalar contraction of the physical moving-frame cut has the
manuscript's massive spectral density, including charge, Fourier
normalization, the center-energy factor and the entire form factor. -/
theorem pair_spin_spectral_disintegration (b : PairSpatialFrame) {m : ℝ} (hm : 0 < m)
    (p ℓ e : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ k : ChargeSpatialMomentum,
      let s := invariantMassSq m (p • b 0) k
      F s * ENNReal.ofReal (e^2/(2*π)^3 * contractedPairSpin m (p • b 0) k *
        exp (-(2*ℓ^4)*s^2))) =
      ∫⁻ s in Ioi (4*m^2), F s * ENNReal.ofReal (s/(2*pairEnergy p s) * (e^2*massDensity m ℓ s)) := by
  let W := fun s : ℝ => e^2/(2*π)^3 * (4*(s+2*m^2)/3) * exp (-(2*ℓ^4)*s^2)
  have hW : Measurable W := by unfold W; fun_prop
  let G := fun s => F s * ENNReal.ofReal (W s)
  have hG : Measurable G := hF.mul hW.ennreal_ofReal
  have hWd {s : ℝ} (hs : 4*m^2 ≤ s) : 0 ≤ W s := by
    have hs₀ : 0 ≤ s := (by positivity : 0 ≤ 4*m^2).trans hs
    unfold W
    positivity
  calc
    _ = ∫⁻ k, G (invariantMassSq m (p • b 0) k) *
        ENNReal.ofReal ((4*energy m k*energy m (p • b 0-k))⁻¹) := by
      apply lintegral_congr
      intro k
      let s := invariantMassSq m (p • b 0) k
      let E := energy m k
      let D := energy m (p • b 0-k)
      have hs := invariantMassSq_threshold hm (p • b 0) k
      have hWs : 0 ≤ W s := hWd hs
      change F s * ENNReal.ofReal (e^2/(2*π)^3 * contractedPairSpin m (p • b 0) k *
        exp (-(2*ℓ^4)*s^2)) = (F s * ENNReal.ofReal (W s)) * ENNReal.ofReal ((4*E*D)⁻¹)
      rw [mul_assoc (F s),← ENNReal.ofReal_mul hWs,contracted_pair_spin hm]
      congr 2
      change e^2/(2*π)^3 * ((s+2*m^2)/(3*E*D)) * exp (-(2*ℓ^4)*s^2) =
        W s * (4*E*D)⁻¹
      unfold W
      ring
    _ = ∫⁻ s in Ioi (4*m^2), G s * ENNReal.ofReal (π/(4*sqrt (p^2+s))*sqrt (1-4*m^2/s)) :=
      pair_invariant_mass_disintegration b hm p G hG
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro s hs
      have hs₀ : 0 < s := (by positivity : 0 < 4*m^2).trans hs
      change (F s * ENNReal.ofReal (W s)) * ENNReal.ofReal (π/(4*sqrt (p^2+s))*sqrt (1-4*m^2/s)) =
        F s * ENNReal.ofReal (s/(2*pairEnergy p s)*(e^2*massDensity m ℓ s))
      rw [mul_assoc,← ENNReal.ofReal_mul (hWd hs.le),massDensity,if_pos hs.le,openingWeight,
        max_eq_left (by positivity : 0 ≤ 4*m^2/s)]
      congr 2
      unfold W pairEnergy
      field_simp [hs₀.ne',pi_pos.ne',(sqrt_pos.mpr (by positivity : 0 < p^2+s)).ne']
      ring

end UV.PairCurvature
