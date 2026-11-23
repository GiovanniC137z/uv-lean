import UV.ContinueThinCurrentExpansion
import UV.ContinueRigidSphereRadial
import UV.ExtendShellMeasureBounds

/-! Spatial harmonic readout of a finite signed polygon at one positive
depth. The carrier frequency runs over the entire real line. -/

noncomputable section

namespace UV

open MeasureTheory Set Real SectorPlane Filter
open scoped ENNReal BigOperators NNReal

def thinPathLength {ι : Type*} [Fintype ι] (edges : ι → ThinCurrentSegment) : ℝ :=
  ∑ i, |((edges i).multiplicity : ℝ)| * (edges i).length

theorem thinCurrentNormSq_le_length_sq {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment) (p : ThinCurrentPlane) :
    thinCurrentNormSq edges p ≤ (thinPathLength edges)^2 := by
  let v := fun i => (WithLp.toLp 2 (fun j => ((edges i).tangent j : ℂ)) : EuclideanSpace ℂ (Fin 4))
  let t := fun i => ((edges i).multiplicity : ℂ)*thinCurrentSegmentWave (edges i) p
  have hv (i : ι) : ‖v i‖ = 1 := by
    have h := EuclideanSpace.norm_sq_eq (v i)
    change ‖v i‖^2 = ∑ j, ‖((edges i).tangent j : ℂ)‖^2 at h
    simp only [Complex.norm_real,← EuclideanSpace.norm_sq_eq,(edges i).unit_tangent,one_pow] at h
    nlinarith only [h,norm_nonneg (v i)]
  have hcomp (j : Fin 4) : (∑ i, t i • v i) j = thinCurrent edges p j := by
    change (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin 4 => ℂ) j) (∑ i, t i • v i) = _
    rw [map_sum]
    unfold thinCurrent
    apply Finset.sum_congr rfl
    intro i _
    change (((edges i).multiplicity : ℂ)*thinCurrentSegmentWave (edges i) p) * ((edges i).tangent j : ℂ) = _
    ring
  have hnorm : ‖∑ i, t i • v i‖ ≤ thinPathLength edges := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul,hv,mul_one]
    change ‖((edges i).multiplicity : ℂ)*thinCurrentSegmentWave (edges i) p‖ ≤ _
    rw [norm_mul,show ((edges i).multiplicity : ℂ) = (((edges i).multiplicity : ℝ):ℂ) by norm_cast,
      Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (thinSegmentWave_norm_le (edges i) p) (abs_nonneg _)
  have h := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  simpa only [EuclideanSpace.norm_sq_eq,hcomp,thinCurrentNormSq] using h

def thinSpatialPoint (ω : ℝ) (k : Spatial) : ThinCurrentPlane :=
  WithLp.toLp 2 (Fin.cons ω (fun i => k i))

theorem thinSpatialPoint_norm_sq (ω : ℝ) (k : Spatial) :
    ‖thinSpatialPoint ω k‖^2 = ω^2+‖k‖^2 := by
  rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,EuclideanSpace.norm_sq_eq k]
  simp [thinSpatialPoint,Real.norm_eq_abs]

theorem thinSmeared_current_transverse {ι : Type*} [Fintype ι] (edges : ι → ThinCurrentSegment)
    (hc : thinCurrentClosed edges) (ω r : ℝ) (k : Spatial) :
    let p := thinSpatialPoint ω k
    (∑ i, (p i : ℂ)*((exp (-r*‖k‖):ℂ)*thinCurrent edges p i)) = 0 := by
  intro p
  calc
    _ = (exp (-r*‖k‖):ℂ)*(∑ i, (p i : ℂ)*thinCurrent edges p i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
    _ = _ := by rw [thinCurrent_transverse edges hc p,mul_zero]

private theorem thin_spatial_radial_integral {r : ℝ} (hr : 0 < r) :
    (∫ k : Spatial, exp (-(2*r*‖k‖))/‖k‖) = π/r^2 := by
  have h := integral_fun_norm_addHaar (volume : Measure Spatial) (fun t : ℝ => exp (-(2*r*t))/t)
  have hm : (volume : Measure Spatial).real (Metric.ball 0 1) = 4*π/3 := by
    rw [measureReal_def,EuclideanSpace.volume_ball_fin_three]
    simp only [ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ π*4/3)]
    ring
  simp only [finrank_euclideanSpace_fin,Nat.reduceSub,hm,nsmul_eq_mul,Nat.cast_ofNat,smul_eq_mul] at h
  rw [h]
  have he : (∫ t : ℝ in Ioi 0, t^2*(exp (-(2*r*t))/t)) = ∫ t : ℝ in Ioi 0, t*exp (-(2*r*t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht' : 0 < t := ht
    field_simp
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 2*r) (by norm_num) (by positivity)
  have hΓ : Gamma 2 = 1 := by simp
  norm_num [hΓ,Real.rpow_two] at hg
  rw [he,hg]
  field_simp
  ring

private theorem thin_spatial_ae_ne_zero : ∀ᵐ k : Spatial ∂volume, k ≠ 0 := by
  simp [ae_iff]

def thinSmearedMajorant (r : ℝ) (z : ℝ × Spatial) : ℝ :=
  exp (-(2*r*‖z.2‖))*(z.1^2+‖z.2‖^2)⁻¹

/-- Normalized four-dimensional absolute integral. The spatial origin
is a null set in the outer integral. -/
theorem thinSmearedMajorant_mass {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (((2*π)^4)⁻¹) *
      (∫⁻ z : ℝ × Spatial, ENNReal.ofReal (thinSmearedMajorant r z)) =
      ENNReal.ofReal (1/(16*π^2*r^2)) := by
  let f := fun k : Spatial => exp (-(2*r*‖k‖))/‖k‖
  have hf : (∫ k, f k) = π/r^2 := thin_spatial_radial_integral hr
  have hfi : Integrable f := Integrable.of_integral_ne_zero (hf.trans_ne (by positivity))
  have hmeas : Measurable (fun z : ℝ × Spatial => thinSmearedMajorant r z) :=
    (measurable_const.mul measurable_snd.norm).neg.exp.mul
      ((measurable_fst.pow_const 2).add (measurable_snd.norm.pow_const 2)).inv
  rw [Measure.volume_eq_prod,lintegral_prod_symm _ hmeas.ennreal_ofReal.aemeasurable]
  have he : (fun k : Spatial => ∫⁻ ω : ℝ, ENNReal.ofReal (thinSmearedMajorant r (ω,k))) =ᵐ[volume]
      fun k => ENNReal.ofReal (π*f k) := by
    filter_upwards [thin_spatial_ae_ne_zero] with k hk
    have h0 := norm_pos_iff.mpr hk
    have hi := (opposite_shell_kernel_integrable h0).const_mul (exp (-(2*r*‖k‖)))
    change (∫⁻ ω : ℝ, ENNReal.ofReal (exp (-(2*r*‖k‖))*oppositeShellKernel ‖k‖ ω)) = _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ω => by
      dsimp [oppositeShellKernel]; positivity)]
    rw [integral_const_mul,opposite_shell_kernel_mass h0]
    congr 1
    dsimp [f]
    ring
  rw [lintegral_congr_ae he,← ofReal_integral_eq_lintegral_ofReal (hfi.const_mul π)
    (Eventually.of_forall fun k => by dsimp [f]; positivity),integral_const_mul,hf,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp [pi_ne_zero]
  ring

/-- The positive finite-mass spectral law is the law of the same current
at the two ends of its squared spatial Dirichlet readout. -/
theorem thinSmeared_current_response_bound {ι : Type*} [Fintype ι] (edges : ι → ThinCurrentSegment)
    (ρ : Measure ℝ≥0) [IsFiniteMeasure ρ] {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (((2*π)^4)⁻¹) * (∫⁻ z : ℝ × Spatial,
      thinCurrentSpectrum ρ (‖thinSpatialPoint z.1 z.2‖^2) *
        ENNReal.ofReal (exp (-(2*r*‖z.2‖))*thinCurrentNormSq edges (thinSpatialPoint z.1 z.2))) ≤
      ENNReal.ofReal (ρ.real univ*(thinPathLength edges)^2/(16*π^2*r^2)) := by
  let M := ρ.real univ
  let L := thinPathLength edges
  let N := ENNReal.ofReal (((2*π)^4)⁻¹)
  have hM : 0 ≤ M := measureReal_nonneg
  have hM' : ENNReal.ofReal M = ρ univ := ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hf (x : ℝ) (hx : 0 < x) : thinCurrentSpectrum ρ x ≤ ENNReal.ofReal (M*x⁻¹) := by
    unfold thinCurrentSpectrum
    rw [ENNReal.ofReal_mul hM,hM',mul_comm,← lintegral_const]
    exact lintegral_mono fun s => ENNReal.ofReal_le_ofReal (by
      rw [one_div]; exact inv_anti₀ hx (le_add_of_nonneg_right s.coe_nonneg))
  have hne : ∀ᵐ z : ℝ × Spatial ∂volume, z.2 ≠ 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae thin_spatial_ae_ne_zero
  have hbound := lintegral_mono_ae (μ := (volume : Measure (ℝ × Spatial))) (hne.mono fun z hz => by
    let x := ‖thinSpatialPoint z.1 z.2‖^2
    let P := exp (-(2*r*‖z.2‖))
    have hx : 0 < x := by
      dsimp [x]
      rw [thinSpatialPoint_norm_sq]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr hz))
    have hp : 0 ≤ P := (exp_pos _).le
    have hsq := thinCurrentNormSq_le_length_sq edges (thinSpatialPoint z.1 z.2)
    calc
      thinCurrentSpectrum ρ x * ENNReal.ofReal (P*thinCurrentNormSq edges (thinSpatialPoint z.1 z.2)) ≤
          ENNReal.ofReal (M*x⁻¹)*ENNReal.ofReal (P*L^2) :=
        mul_le_mul' (hf x hx) (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsq hp))
      _ = ENNReal.ofReal (M*L^2)*ENNReal.ofReal (thinSmearedMajorant r z) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hM (inv_nonneg.mpr hx.le)),← ENNReal.ofReal_mul (mul_nonneg hM (sq_nonneg _))]
        congr 1
        dsimp [x,P,thinSmearedMajorant]
        rw [thinSpatialPoint_norm_sq]
        ring)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hbound
  apply (mul_le_mul_left' hbound N).trans_eq
  rw [mul_left_comm]
  dsimp only [N]
  rw [thinSmearedMajorant_mass hr,← ENNReal.ofReal_mul (mul_nonneg hM (sq_nonneg _))]
  congr 1
  ring

end UV
