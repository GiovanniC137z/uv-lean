import UV.ContinueCollarGreen
import UV.ContinueCollarCompactBasis
import UV.ContinueCollarHSIdentity
import Mathlib.MeasureTheory.Integral.Prod

/-! The displayed zero-energy Green kernel acts as a concrete, bounded
symmetric operator on the real radial Hilbert space. -/

noncomputable section

open MeasureTheory Set Real
open UV.ContinueCollarHSIdentity (radialMeasure)
open scoped InnerProductSpace

namespace UV.CollarEigenmode

abbrev RealRadialL2 := Lp ℝ 2 radialMeasure

private instance : IsFiniteMeasure radialMeasure := ⟨by simp [radialMeasure,Real.volume_Ioc]⟩

/-- Extend the unit-interval kernel by zero outside the radial chart. -/
def collarGreenKernel (c r s : ℝ) := if r ∈ Ioc (0:ℝ) 1 ∧ s ∈ Ioc (0:ℝ) 1 then green c r s else 0

theorem collarGreenKernel_symm (c r s : ℝ) : collarGreenKernel c r s=collarGreenKernel c s r := by
  by_cases hr : r ∈ Ioc (0:ℝ) 1 <;> by_cases hs : s ∈ Ioc (0:ℝ) 1 <;> simp [collarGreenKernel,hr,hs,green_symm c r s]

theorem collarGreenKernel_measurable (c : ℝ) : Measurable (fun p : ℝ × ℝ => collarGreenKernel c p.1 p.2) := by
  exact (green_measurable c).ite (measurableSet_Ioc.prod measurableSet_Ioc) measurable_const

theorem collarGreenKernel_bound {c : ℝ} (hc : 0<c) (r s : ℝ) : ‖collarGreenKernel c r s‖ ≤ (6*c)⁻¹ := by
  unfold collarGreenKernel
  split_ifs with h
  · obtain ⟨hp,hu⟩ := green_bounds hc h.1 h.2
    simpa only [Real.norm_of_nonneg hp] using hu
  · simp [hc.le]

private def radialOne : RealRadialL2 := (memLp_const (μ := radialMeasure) (p := 2) (1:ℝ)).toLp _

private theorem radialOne_coe : ∀ᵐ r ∂radialMeasure,radialOne r=1 := MemLp.coeFn_toLp _

private theorem greenRowMem {c : ℝ} (hc : 0<c) (r : ℝ) : MemLp (collarGreenKernel c r) 2 radialMeasure :=
  MemLp.of_bound ((collarGreenKernel_measurable c).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable _
    (Filter.Eventually.of_forall (collarGreenKernel_bound hc r))

def greenRow {c : ℝ} (hc : 0<c) (r : ℝ) : RealRadialL2 := (greenRowMem hc r).toLp _

theorem greenRow_coe {c : ℝ} (hc : 0<c) (r : ℝ) :
    ∀ᵐ s ∂radialMeasure,greenRow hc r s=collarGreenKernel c r s := (greenRowMem hc r).coeFn_toLp

private theorem greenRow_bound {c : ℝ} (hc : 0<c) (r : ℝ) :
    ‖greenRow hc r‖ ≤ (6*c)⁻¹*‖radialOne‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [greenRow_coe hc r,radialOne_coe] with s hs h1
  simpa [hs,h1] using collarGreenKernel_bound hc r s

theorem greenRow_uniform {c : ℝ} (hc : 0<c) : ∃ B : ℝ,0 ≤ B ∧ ∀ r,‖greenRow hc r‖ ≤ B :=
  ⟨_,mul_nonneg (by positivity) (norm_nonneg _),greenRow_bound hc⟩

theorem greenRow_pair {c : ℝ} (hc : 0<c) (r : ℝ) (f : RealRadialL2) :
    ⟪greenRow hc r,f⟫_ℝ = ∫ s,collarGreenKernel c r s*f s ∂radialMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [greenRow_coe hc r] with s hs
  simp [hs,mul_comm]

private theorem integralGreenMem {c : ℝ} (hc : 0<c) (f : RealRadialL2) :
    MemLp (fun r => ⟪greenRow hc r,f⟫_ℝ) 2 radialMeasure := by
  refine MemLp.of_bound ?_ ((6*c)⁻¹*‖radialOne‖*‖f‖) ?_
  · simp_rw [greenRow_pair]
    exact ((collarGreenKernel_measurable c).mul ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right' (ν := radialMeasure) |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun r => (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (greenRow_bound hc r) (norm_nonneg _)))

private def greenLinear {c : ℝ} (hc : 0<c) : RealRadialL2 →ₗ[ℝ] RealRadialL2 where
  toFun f := (integralGreenMem hc f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(integralGreenMem hc (f+g)).coeFn_toLp,Lp.coeFn_add ((integralGreenMem hc f).toLp _) ((integralGreenMem hc g).toLp _),
      (integralGreenMem hc f).coeFn_toLp,(integralGreenMem hc g).coeFn_toLp] with r hr ha hf hg
    rw [hr,ha,Pi.add_apply,hf,hg,inner_add_right]
  map_smul' k f := by
    apply Lp.ext
    filter_upwards [(integralGreenMem hc (k • f)).coeFn_toLp,Lp.coeFn_smul k ((integralGreenMem hc f).toLp _),(integralGreenMem hc f).coeFn_toLp] with r hr ha hf
    rw [RingHom.id_apply,hr,ha,Pi.smul_apply,hf,real_inner_smul_right,smul_eq_mul]

def greenOperator {c : ℝ} (hc : 0<c) : RealRadialL2 →L[ℝ] RealRadialL2 :=
  (greenLinear hc).mkContinuous ((6*c)⁻¹*‖radialOne‖^2) (fun f => by
    have hb : ‖greenLinear hc f‖ ≤ ((6*c)⁻¹*‖radialOne‖*‖f‖)*‖radialOne‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [(integralGreenMem hc f).coeFn_toLp,radialOne_coe] with r hr h1
      change ‖((integralGreenMem hc f).toLp _) r‖ ≤ _
      rw [hr,h1,norm_one,mul_one]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (greenRow_bound hc r) (norm_nonneg _))
    convert hb using 1; ring)

theorem greenOperator_coe {c : ℝ} (hc : 0<c) (f : RealRadialL2) :
    ∀ᵐ r ∂radialMeasure,greenOperator hc f r=∫ s,collarGreenKernel c r s*f s ∂radialMeasure :=
  (integralGreenMem hc f).coeFn_toLp.mono fun r hr => hr.trans (greenRow_pair hc r f)

private theorem green_pair_integrable {c : ℝ} (hc : 0<c) (f g : RealRadialL2) :
    Integrable (fun p : ℝ × ℝ => g p.1*(collarGreenKernel c p.1 p.2*f p.2)) (radialMeasure.prod radialMeasure) := by
  have hf : Integrable (fun x => ‖f x‖) radialMeasure := ((Lp.memLp f).integrable (by norm_num)).norm
  have hg : Integrable (fun x => ‖g x‖) radialMeasure := ((Lp.memLp g).integrable (by norm_num)).norm
  apply ((hg.mul_prod hf).const_mul ((6*c)⁻¹)).mono'
  · exact (((Lp.stronglyMeasurable g).measurable.comp measurable_fst).mul
      ((collarGreenKernel_measurable c).mul ((Lp.stronglyMeasurable f).measurable.comp measurable_snd))).aestronglyMeasurable
  · filter_upwards with p
    rw [norm_mul,norm_mul]
    change _ ≤ (6*c)⁻¹*(‖g p.1‖*‖f p.2‖)
    calc
      _ ≤ ‖g p.1‖*((6*c)⁻¹*‖f p.2‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (collarGreenKernel_bound hc _ _) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring

theorem greenOperator_symmetric {c : ℝ} (hc : 0<c) : (greenOperator hc).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪greenOperator hc f,g⟫_ℝ = ⟪f,greenOperator hc g⟫_ℝ
  rw [L2.inner_def,L2.inner_def]
  calc
    _ = ∫ r,∫ s,g r*(collarGreenKernel c r s*f s) ∂radialMeasure ∂radialMeasure := by
      apply integral_congr_ae
      filter_upwards [greenOperator_coe hc f] with r hr
      rw [integral_const_mul]
      change g r*greenOperator hc f r=_
      rw [hr]
    _ = ∫ s,∫ r,g r*(collarGreenKernel c r s*f s) ∂radialMeasure ∂radialMeasure :=
      integral_integral_swap (green_pair_integrable hc f g)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [greenOperator_coe hc g] with s hs
      change _ = greenOperator hc g s*f s
      rw [hs,←integral_mul_const]
      apply integral_congr_ae
      filter_upwards with r
      rw [collarGreenKernel_symm c s r]
      ring

end UV.CollarEigenmode
