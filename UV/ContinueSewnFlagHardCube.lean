import UV.HeatFourier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Normalized averages on the four-dimensional hard cubes
`[R,2R]^4` in the original Euclidean momentum coordinates. -/

noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal RealInnerProductSpace Topology
namespace UV.SewnFlags

private def hardCubeCoordinates (R : ℝ) : Set (Fin 4 → ℝ) :=
  univ.pi (fun _ => Icc R (2*R))

def hardCube (R : ℝ) : Set ScalarMomentum := WithLp.ofLp ⁻¹' hardCubeCoordinates R

theorem hardCube_measurable (R : ℝ) : MeasurableSet (hardCube R) :=
  (MeasurableSet.univ_pi fun _ => measurableSet_Icc).preimage (EuclideanSpace.measurableEquiv (Fin 4)).measurable

theorem hardCube_norm_bounds {R : ℝ} (hR : 0 ≤ R) {k : ScalarMomentum} (hk : k ∈ hardCube R) :
    R ≤ ‖k‖ ∧ ‖k‖ ≤ 4*R := by
  have h (j : Fin 4) : k j ∈ Icc R (2*R) := mem_pi.mp hk j (mem_univ j)
  refine ⟨(h 0).1.trans ((le_abs_self _).trans (PiLp.norm_apply_le k 0)), ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _ : Fin 4, (2*R)^2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [Real.norm_of_nonneg (hR.trans (h j).1)]
      exact (sq_le_sq₀ (hR.trans (h j).1) (by positivity)).mpr (h j).2
    _ = (4*R)^2 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem hardCube_eventually_excludes (k : ScalarMomentum) :
    ∀ᶠ R : ℝ in atTop, k ∉ hardCube R := by
  filter_upwards [eventually_gt_atTop ‖k‖] with R hR hk
  exact hR.not_ge (hardCube_norm_bounds ((norm_nonneg _).trans hR.le) hk).1

def hardCubeMeasure (R : ℝ) : Measure ScalarMomentum :=
  ENNReal.ofReal ((R^4)⁻¹) • (volume.restrict (hardCube R))

theorem hardCube_volume (R : ℝ) (hR : 0 ≤ R) :
    (volume : Measure ScalarMomentum) (hardCube R) = ENNReal.ofReal (R^4) := by
  have h := (PiLp.volume_preserving_ofLp (Fin 4)).map_eq
  have hP : MeasurableSet (hardCubeCoordinates R) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  rw [hardCube,← Measure.map_apply (PiLp.volume_preserving_ofLp (Fin 4)).measurable hP,h,
    volume_pi,hardCubeCoordinates,Measure.pi_pi]
  simp only [Real.volume_Icc,show 2*R-R = R by ring,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [ENNReal.ofReal_pow hR]

theorem hardCubeMeasure_univ {R : ℝ} (hR : 0 < R) : hardCubeMeasure R univ = 1 := by
  unfold hardCubeMeasure
  rw [Measure.smul_apply,Measure.restrict_apply_univ,hardCube_volume R hR.le,smul_eq_mul,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hR.le _)), inv_mul_cancel₀ (pow_ne_zero _ hR.ne'),
    ENNReal.ofReal_one]

private def intervalPhase (R x : ℝ) : ℂ :=
  ((R⁻¹:ℝ):ℂ) * ∫ t in Icc R (2*R), Complex.exp (Complex.I * (x:ℂ) * (t:ℂ))

private theorem linePhase_norm (x t : ℝ) : ‖Complex.exp (Complex.I * (x:ℂ) * (t:ℂ))‖ = 1 := by
  simp [Complex.norm_exp,Complex.mul_re]

private theorem intervalPhase_bound {R : ℝ} (hR : 0 < R) (x : ℝ) : ‖intervalPhase R x‖ ≤ 1 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := R) (b := 2*R)
    (f := fun t : ℝ => Complex.exp (Complex.I * (x:ℂ) * (t:ℂ))) (C := 1)
    (fun t _ => (linePhase_norm x t).le)
  have hR' : R ≤ 2*R := by linarith
  rw [intervalIntegral.integral_of_le hR',← integral_Icc_eq_integral_Ioc,
    show 2*R-R = R by ring,abs_of_pos hR,one_mul] at h
  unfold intervalPhase
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr hR).le]
  exact (mul_le_mul_of_nonneg_left h (inv_pos.mpr hR).le).trans_eq (inv_mul_cancel₀ hR.ne')

private theorem intervalPhase_zero {R : ℝ} (hR : 0 < R) : intervalPhase R 0 = 1 := by
  unfold intervalPhase
  have he : (fun t : ℝ => Complex.exp (Complex.I * ((0:ℝ):ℂ) * (t:ℂ))) = fun _ => 1 := by
    funext t
    simp only [Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero]
  rw [he,setIntegral_const,Real.volume_real_Icc,show 2*R-R = R by ring,
    max_eq_left hR.le,Complex.real_smul,mul_one]
  exact_mod_cast inv_mul_cancel₀ hR.ne'

private theorem intervalPhase_decay (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun R : ℝ => intervalPhase R x) atTop (𝓝 0) := by
  have hC : Tendsto (fun R : ℝ => R⁻¹ * (2/|x|)) atTop (𝓝 0) := by
    simpa only [zero_mul] using tendsto_inv_atTop_zero.mul_const (2/|x|)
  apply squeeze_zero_norm' _ hC
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  have hR' : R ≤ 2*R := by linarith
  let c := Complex.I * (x:ℂ)
  have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hx)
  unfold intervalPhase
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr hR).le,
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hR',integral_exp_mul_complex hc,norm_div]
  have hnorm : ‖c‖ = |x| := by simp [c]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hR).le
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  exact (norm_sub_le _ _).trans_eq (by rw [show ‖Complex.exp (c*((2*R:ℝ):ℂ))‖ = 1 from linePhase_norm x _,
    show ‖Complex.exp (c*(R:ℂ))‖ = 1 from linePhase_norm x _]; norm_num)

def hardCubePhaseMean (R : ℝ) (d : ScalarMomentum) : ℂ :=
  ∫ k, stableFourierPhase d k ∂hardCubeMeasure R

private theorem hardCubePhaseMean_eq_prod {R : ℝ} (hR : 0 < R) (d : ScalarMomentum) :
    hardCubePhaseMean R d = ∏ j : Fin 4, intervalPhase R (d j) := by
  let f := fun j (t : ℝ) => Complex.exp (Complex.I * (d j:ℂ) * (t:ℂ))
  have hF (k : ScalarMomentum) : stableFourierPhase d k = ∏ j, f j (k j) := by
    unfold stableFourierPhase f
    rw [PiLp.inner_apply,Complex.ofReal_sum,Finset.mul_sum,Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    rw [RCLike.inner_apply,conj_trivial, Complex.ofReal_mul,mul_assoc,mul_comm (d j:ℂ)]
  unfold hardCubePhaseMean hardCubeMeasure
  rw [integral_smul_measure,ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hR.le _))]
  simp_rw [hF]
  have hM := (PiLp.volume_preserving_ofLp (Fin 4)).setIntegral_preimage_emb
    (EuclideanSpace.measurableEquiv (Fin 4)).measurableEmbedding
    (fun k : Fin 4 → ℝ => ∏ j, f j (k j)) (hardCubeCoordinates R)
  change (∫ k in hardCube R, ∏ j, f j (k j)) = _ at hM
  rw [hM,hardCubeCoordinates,volume_pi,Measure.restrict_pi_pi,integral_fintype_prod_eq_prod f]
  simp only [intervalPhase,Complex.real_smul,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Complex.ofReal_pow,← inv_pow, f]

theorem hardCubePhaseMean_bound {R : ℝ} (hR : 0 < R) (d : ScalarMomentum) :
    ‖hardCubePhaseMean R d‖ ≤ 1 := by
  rw [hardCubePhaseMean_eq_prod hR,norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => intervalPhase_bound hR _)

theorem hardCubePhaseMean_measurable (R : ℝ) : Measurable (hardCubePhaseMean R) := by
  letI : SFinite (hardCubeMeasure R) := by unfold hardCubeMeasure; infer_instance
  exact stableFourierPhase_continuous.measurable.stronglyMeasurable.integral_prod_right'.measurable

theorem hardCubePhaseMean_limit (d : ScalarMomentum) :
    Tendsto (fun R : ℝ => hardCubePhaseMean R d) atTop (𝓝 (if d = 0 then 1 else 0)) := by
  classical
  have hEq : (fun R : ℝ => hardCubePhaseMean R d) =ᶠ[atTop] (fun R => ∏ j : Fin 4, intervalPhase R (d j)) :=
    (eventually_gt_atTop (0:ℝ)).mono fun _ hR => hardCubePhaseMean_eq_prod hR d
  rw [tendsto_congr' hEq]
  have h (j : Fin 4) : Tendsto (fun R : ℝ => intervalPhase R (d j)) atTop (𝓝 (if d j = 0 then 1 else 0)) := by
    split_ifs with hj
    · rw [hj]
      exact tendsto_const_nhds.congr' ((eventually_gt_atTop (0:ℝ)).mono
        fun _ hR => (intervalPhase_zero hR).symm)
    · exact intervalPhase_decay _ hj
  have hp := tendsto_finset_prod Finset.univ (fun j _ => h j)
  convert hp using 2
  split_ifs with hD
  · simp [hD]
  · have hj : ∃ j, d j ≠ 0 := by
      contrapose! hD
      apply WithLp.ofLp_injective
      exact funext hD
    obtain ⟨j,hj⟩ := hj
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)]

end UV.SewnFlags
