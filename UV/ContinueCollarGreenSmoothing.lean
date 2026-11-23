import UV.ContinueCollarGreenOperator
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Regularity of the Green inverse on the singular radial interval:
every square-integrable source has a continuous Dirichlet response, and
every nonzero Green eigenvalue gives a classical radial eigenfunction. -/

noncomputable section

open MeasureTheory Set Real Filter
open UV.ContinueCollarHSIdentity (radialMeasure)
open scoped Topology

namespace UV.CollarEigenmode

private instance : IsFiniteMeasure radialMeasure := ⟨by simp [radialMeasure,Real.volume_Ioc]⟩

theorem collarGreenKernel_continuous {c : ℝ} (hc : 0<c) (s : ℝ) : Continuous fun r => collarGreenKernel c r s := by
  by_cases hs : s ∈ Ioc (0:ℝ) 1
  · let q (x : ℝ) := max 0 (min x 1)
    have hq : Continuous q := continuous_const.max (continuous_id.min continuous_const)
    have hqS (x : ℝ) : q x ∈ Icc (0:ℝ) 1 := ⟨le_max_left ..,max_le zero_le_one (min_le_right ..)⟩
    have hmin : Continuous fun x => barrier c (min (q x) s) := by
      apply (barrier_continuous (h := 1) hc).comp_continuous (hq.min continuous_const)
      exact fun x => ⟨le_min (hqS x).1 hs.1.le,(min_le_left ..).trans (hqS x).2⟩
    have hmax : Continuous fun x => rightSolution c (max (q x) s) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact ContinuousAt.comp (g := rightSolution c) (f := fun y => max (q y) s) (right_hasDerivAt c (hs.1.trans_le (le_max_right (q x) s))).continuousAt (hq.max continuous_const).continuousAt
    have h := (hmin.mul hmax).div_const (6*c)
    convert h using 1
    ext x
    by_cases h₀ : 0<x
    · by_cases h₁ : x ≤ 1
      · simp [collarGreenKernel,hs,h₀,h₁,green,q,max_eq_right h₀.le]
      · have hq₁ : q x=1 := by simp [q,min_eq_right (le_of_not_ge h₁)]
        have hd := (green_dirichlet_values c s ⟨hs.1.le,hs.2⟩).2
        simpa [collarGreenKernel,hs,h₁,hq₁,green] using hd.symm
    · have hq₀ : q x=0 := max_eq_left ((min_le_left ..).trans (le_of_not_gt h₀))
      have hd := (green_dirichlet_values c s ⟨hs.1.le,hs.2⟩).1
      simpa [collarGreenKernel,hs,h₀,hq₀,green] using hd.symm
  · simpa [collarGreenKernel,hs] using (continuous_const : Continuous fun _ : ℝ => (0:ℝ))

def greenResponse (c : ℝ) (f : RealRadialL2) (r : ℝ) := ∫ s,collarGreenKernel c r s*f s ∂radialMeasure

theorem greenResponse_continuous {c : ℝ} (hc : 0<c) (f : RealRadialL2) : Continuous (greenResponse c f) := by
  apply continuous_of_dominated (bound := fun s => (6*c)⁻¹*‖f s‖)
  · intro r
    exact (((collarGreenKernel_measurable c).comp (measurable_const.prodMk measurable_id)).mul (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable
  · exact fun r => Eventually.of_forall fun s => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (collarGreenKernel_bound hc r s) (norm_nonneg _)
  · exact ((Lp.memLp f).integrable (by norm_num)).norm.const_mul _
  · exact Eventually.of_forall fun s => (collarGreenKernel_continuous hc s).mul continuous_const

theorem greenResponse_dirichlet (c : ℝ) (f : RealRadialL2) : greenResponse c f 0=0 ∧ greenResponse c f 1=0 := by
  constructor
  · simp [greenResponse,collarGreenKernel]
  · apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (s := Ioc (0:ℝ) 1) measurableSet_Ioc] with s hs
    simp [collarGreenKernel,hs,(green_dirichlet_values c s ⟨hs.1.le,hs.2⟩).2]

theorem greenResponse_at_continuous {c : ℝ} (hc : 0<c) (f : RealRadialL2) (u : ℝ → ℝ)
    (hC : Continuous u) (hf : ∀ᵐ s ∂radialMeasure,f s=u s) {r : ℝ} (hr : r ∈ Ioo 0 1) :
    greenResponse c f r = greenApplied c u r := by
  rw [greenApplied_eq_integral hc u hC hr,intervalIntegral.integral_of_le zero_le_one]
  apply integral_congr_ae
  filter_upwards [hf,ae_restrict_mem (s := Ioc (0:ℝ) 1) measurableSet_Ioc] with s h₁ hs
  simp [collarGreenKernel,hs,hr.1,hr.2.le,h₁]

theorem greenOperator_classical_mode {c e : ℝ} (hc : 0<c) (he : e ≠ 0)
    (f : RealRadialL2) (hef : greenOperator hc f=e • f) :
    ∃ u g : ℝ → ℝ,Continuous u ∧ u 0=0 ∧ u 1=0 ∧ (∀ᵐ r ∂radialMeasure,f r=u r) ∧
      (∀ r ∈ Ioo 0 1,HasDerivAt u (g r) r) ∧
      (∀ r ∈ Ioo 0 1,HasDerivAt g ((potential (3*c) r-e⁻¹)*u r) r) := by
  let u := fun r => greenResponse c f r/e
  let g := fun r => greenGradient c u r/e
  have hC : Continuous u := (greenResponse_continuous hc f).div_const e
  have hf : ∀ᵐ r ∂radialMeasure,f r=u r := by
    filter_upwards [greenOperator_coe hc f,Lp.coeFn_smul e f] with r hr hs
    rw [hef,hs,Pi.smul_apply,smul_eq_mul] at hr
    exact (eq_div_iff he).mpr ((mul_comm ..).trans hr)
  have H (r : ℝ) (hr : r ∈ Ioo 0 1) : greenResponse c f r=greenApplied c u r :=
    greenResponse_at_continuous hc f u hC hf hr
  obtain ⟨h₀,h₁⟩ := greenResponse_dirichlet c f
  refine ⟨u,g,hC,by simp [u,h₀],by simp [u,h₁],hf,?_,?_⟩
  · intro r hr
    have h := (green_solves hc u hC hr).1.div_const e
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
    exact congrArg (fun z : ℝ => z/e) (H x hx)
  · intro r hr
    have h := (green_solves hc u hC hr).2.div_const e
    convert h using 1
    rw [← H r hr]
    dsimp [u]
    field_simp

end UV.CollarEigenmode
