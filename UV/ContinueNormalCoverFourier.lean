import UV.ContinueNormalOpenDirac

/-! The Fourier transform of the signed normal-circle cover kernel, in
angular frequency. The value at the jump is immaterial to the integral.
The real normal coordinate is independent of the sector's unit GT pole. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set UV.SectorPlane
open scoped Matrix Matrix.Norms.L2Operator Topology

namespace UV

def normalCoverGamma5 : DiracMatrix := euclideanGamma 0*euclideanGamma 1*euclideanGamma 2*euclideanGamma 3

theorem normal_cover_gamma_norm : ‖normalCoverGamma5‖ = 1 := by
  have hg (j : Fin 4) : euclideanGamma j ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change (euclideanGamma j)ᴴ * euclideanGamma j = 1
    rw [euclideanGamma_isHermitian j]
    ext i k
    have h := congrArg (fun A : DiracMatrix => A i k) (euclideanGamma_clifford j j)
    simp only [if_true,two_smul,Matrix.add_apply] at h
    linear_combination (1/2:ℂ)*h
  have h : normalCoverGamma5 ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
    mul_mem (mul_mem (mul_mem (hg 0) (hg 1)) (hg 2)) (hg 3)
  exact CStarRing.norm_of_mem_unitary h

/-- The representative at the origin is the midpoint of the two normal
one-sided limits. Their difference is exactly the chirality insertion. -/
theorem normal_cover_oriented_jump (J : DiracMatrix) (m : ℝ) (p : OSFourSpace) :
    let B := (1/(2*(normalCoverEnergy m p:ℂ))) • freeDiracNumerator m p
    let H := (1/2:ℂ) • J
    Tendsto (normalDiracCover J m p) (𝓝[>] (0:ℝ)) (𝓝 (B+H)) ∧
      Tendsto (normalDiracCover J m p) (𝓝[<] (0:ℝ)) (𝓝 (B-H)) ∧
      normalDiracCover J m p 0 = B ∧ (B+H)-(B-H) = J := by
  let B := (1/(2*(normalCoverEnergy m p:ℂ))) • freeDiracNumerator m p
  let H := (1/2:ℂ) • J
  let f := fun d : ℝ => ((Real.exp (-normalCoverEnergy m p*|d|) : ℝ) : ℂ)
  have hc : Continuous f := by dsimp [f]; fun_prop
  have ht : Tendsto f (𝓝 0) (𝓝 (1:ℂ)) := by simpa [f] using (hc.continuousAt (x := (0:ℝ))).tendsto
  refine ⟨?_,?_,?_,?_⟩
  · have h := (ht.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))).smul_const (B+H)
    rw [one_smul] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with d hd
    simp [normalDiracCover,Real.sign_of_pos (show 0 < d from hd),B,H,f]
  · have h := (ht.mono_left (nhdsWithin_le_nhds (s := Iio (0:ℝ)))).smul_const (B-H)
    rw [one_smul] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with d hd
    simp [normalDiracCover,Real.sign_of_neg (show d < 0 from hd),B,H,f,sub_eq_add_neg]
    module
  · simp [normalDiracCover]
  · dsimp only [B,H]; module

/-- The transform in the normal variable equals the full free multiplier,
including the sign of the gamma-five numerator in angular frequency. -/
theorem normal_cover_angular_fourier (J : DiracMatrix) {m : ℝ} (hm : 0 < m) (p : OSFourSpace) (ξ : ℝ) :
    let E := normalCoverEnergy m p
    let f := fun d : ℝ => Complex.exp (-Complex.I*(ξ:ℂ)*d) • normalDiracCover J m p d
    Integrable f ∧ (∫ d, f d) = (((E^2+ξ^2 : ℝ):ℂ)⁻¹) •
      (freeDiracNumerator m p + (-Complex.I*(ξ:ℂ)) • J) := by
  let E := normalCoverEnergy m p
  let N := freeDiracNumerator m p
  let B := (1/(2*(E:ℂ))) • N
  let H := (1/2:ℂ) • J
  let a : ℂ := (E:ℂ)-Complex.I*(ξ:ℂ)
  let b : ℂ := -(E:ℂ)-Complex.I*(ξ:ℂ)
  let f := fun d : ℝ => Complex.exp (-Complex.I*(ξ:ℂ)*d) • normalDiracCover J m p d
  have hE : 0 < E := hm.trans_le (normal_cover_energy_bounds hm p).1
  have ha : 0 < a.re := by simpa [a] using hE
  have hb : b.re < 0 := by simpa [b] using neg_lt_zero.mpr hE
  have hneg (d : ℝ) (hd : d < 0) : f d = Complex.exp (a*d) • (B-H) := by
    simp only [f,normalDiracCover,Real.sign_of_neg hd,abs_of_neg hd,Complex.ofReal_exp,
      smul_smul,←Complex.exp_add,Complex.ofReal_mul,Complex.ofReal_neg]
    congr 1
    · congr 1; dsimp [a,E]; ring
    · dsimp [B,H,N,E]; module
  have hpos (d : ℝ) (hd : 0 < d) : f d = Complex.exp (b*d) • (B+H) := by
    simp only [f,normalDiracCover,Real.sign_of_pos hd,abs_of_pos hd,Complex.ofReal_exp,
      smul_smul,←Complex.exp_add,Complex.ofReal_mul,Complex.ofReal_neg]
    congr 1
    · congr 1; dsimp [b,E]; ring
    · dsimp [B,H,N,E]; module
  have hL : f =ᵐ[volume.restrict (Iic (0:ℝ))] (fun d : ℝ => Complex.exp (a*d) • (B-H)) := by
    rw [←restrict_Iio_eq_restrict_Iic]
    exact ae_restrict_of_forall_mem measurableSet_Iio hneg
  have hR : f =ᵐ[volume.restrict (Ioi (0:ℝ))] (fun d : ℝ => Complex.exp (b*d) • (B+H)) :=
    ae_restrict_of_forall_mem measurableSet_Ioi hpos
  have hiL : IntegrableOn f (Iic (0:ℝ)) := ((integrableOn_exp_mul_complex_Iic ha 0).smul_const (B-H)).congr hL.symm
  have hiR : IntegrableOn f (Ioi (0:ℝ)) := ((integrableOn_exp_mul_complex_Ioi hb 0).smul_const (B+H)).congr hR.symm
  refine ⟨by simpa only [Iic_union_Ioi,IntegrableOn,Measure.restrict_univ] using hiL.union hiR,?_⟩
  change (∫ d, f d) = _
  rw [←intervalIntegral.integral_Iic_add_Ioi hiL hiR,integral_congr_ae hL,integral_congr_ae hR,
    integral_smul_const,integral_smul_const,integral_exp_mul_complex_Iic ha 0,integral_exp_mul_complex_Ioi hb 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have he0 : (E:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hE.ne'
  have hD : ((E^2+ξ^2 : ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hab : a*b = -((E^2+ξ^2 : ℝ):ℂ) := by
    dsimp [a,b]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  change (1/a) • (B-H) + (-1/b) • (B+H) = (((E^2+ξ^2 : ℝ):ℂ)⁻¹) • (N+(-Complex.I*(ξ:ℂ)) • J)
  have hden : ((E^2+ξ^2 : ℝ):ℂ) = -(a*b) := by rw [hab,neg_neg]
  rw [hden]
  dsimp only [B,H]
  match_scalars
  all_goals
    field_simp [ha0,hb0,he0]
    dsimp only [a,b]
    ring

/-- Read the carrier momentum in the oriented chart of the fixed sector.
The oriented normal Fourier variable and its gamma-five numerator are
independent of the sector's GT boundary prescription. -/
theorem SectorPlane.Plane.normal_cover_fourier_chart {E : Type*} [Norm E] (diamond : Plane E)
    {m : ℝ} (hm : 0 < m) (p : OSFourSpace) (ξ : ℝ) :
    let k := diamond.osOrientedChart p
    let f := fun d : ℝ => Complex.exp (-Complex.I*(ξ:ℂ)*d) • normalDiracCover normalCoverGamma5 m k d
    Integrable f ∧ (∫ d, f d) = (((normalCoverEnergy m p)^2+ξ^2 : ℝ):ℂ)⁻¹ •
      (freeDiracNumerator m k + (-Complex.I*(ξ:ℂ)) • normalCoverGamma5) := by
  simpa only [normalCoverEnergy,diamond.osOrientedChart.norm_map] using
    normal_cover_angular_fourier normalCoverGamma5 hm (diamond.osOrientedChart p) ξ

end UV
