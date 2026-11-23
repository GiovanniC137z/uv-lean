import UV.ContinueHeatMaxwellGaussianBounds

/-! A common Gaussian majorant permits twice differentiating the full
soft loop after a smooth finite-dimensional contraction of its marks. -/

noncomputable section
namespace UV.HeatMaxwell
open UV.SectorPlane MeasureTheory Filter Set Metric
open scoped Topology

local instance continueHeatMaxwellLoopDerivMeasurableSpace : MeasurableSpace EuclideanPlaneMomentum := borel _
local instance continueHeatMaxwellLoopDerivBorelSpace : BorelSpace EuclideanPlaneMomentum := ⟨rfl⟩

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

structure HeatLoopCurve where
  value : ℝ → EuclideanPlaneMomentum → E
  first : ℝ → EuclideanPlaneMomentum → E
  second : ℝ → EuclideanPlaneMomentum → E
  deriv_value : ∀ t k, HasDerivAt (fun s => value s k) (first t k) t
  deriv_first : ∀ t k, HasDerivAt (fun s => first s k) (second t k) t
  measurable_value : ∀ t, AEStronglyMeasurable (value t)
  measurable_first : ∀ t, AEStronglyMeasurable (first t)
  measurable_second : ∀ t, AEStronglyMeasurable (second t)
  gaussian_bound : ∃ C : ℝ, 0≤C ∧ ∀ t k, |t|≤1 →
    ‖value t k‖ ≤ C*heatLoopMajorant k ∧ ‖first t k‖ ≤ C*heatLoopMajorant k ∧ ‖second t k‖ ≤ C*heatLoopMajorant k

variable {E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def HeatLoopCurve.pair (a : HeatLoopCurve E) (b : HeatLoopCurve F) : HeatLoopCurve (E×F) where
  value t k := (a.value t k,b.value t k)
  first t k := (a.first t k,b.first t k)
  second t k := (a.second t k,b.second t k)
  deriv_value t k := (a.deriv_value t k).prodMk (b.deriv_value t k)
  deriv_first t k := (a.deriv_first t k).prodMk (b.deriv_first t k)
  measurable_value t := (a.measurable_value t).prodMk (b.measurable_value t)
  measurable_first t := (a.measurable_first t).prodMk (b.measurable_first t)
  measurable_second t := (a.measurable_second t).prodMk (b.measurable_second t)
  gaussian_bound := by
    obtain ⟨A,hA,ha⟩ := a.gaussian_bound
    obtain ⟨B,hB,hb⟩ := b.gaussian_bound
    refine ⟨max A B,le_max_of_le_left hA,?_⟩
    intro t k ht
    have h1 : A*heatLoopMajorant k≤max A B*heatLoopMajorant k := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
    have h2 : B*heatLoopMajorant k≤max A B*heatLoopMajorant k := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
    obtain ⟨av,af,as'⟩ := ha t k ht
    obtain ⟨bv,bf,bs⟩ := hb t k ht
    exact ⟨max_le (av.trans h1) (bv.trans h2),max_le (af.trans h1) (bf.trans h2),max_le (as'.trans h1) (bs.trans h2)⟩

private theorem heat_loop_majorant_le_one (k : EuclideanPlaneMomentum) : heatLoopMajorant k≤1 :=
  Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖k‖])

set_option maxHeartbeats 900000 in
/-- A C² smooth contraction on the joint range has bounded first two
Fréchet derivatives on the compact ball containing all marked vectors. -/
def HeatLoopCurve.compose [FiniteDimensional ℝ E] (a : HeatLoopCurve E) {G : E→F}
    (hG : ContDiff ℝ 2 G) (h0 : G 0=0) : HeatLoopCurve F := by
  let D := fderiv ℝ G
  let H := fderiv ℝ D
  have hD : ContDiff ℝ 1 D := hG.fderiv_right (by norm_num)
  have hDc : Continuous D := hD.continuous
  have hHc : Continuous H := hD.continuous_fderiv (by norm_num)
  have hdG (x) := (hG.differentiable (by norm_num) x).hasFDerivAt
  have hdD (x) := (hD.differentiable (by norm_num) x).hasFDerivAt
  refine {
    value := fun t k => G (a.value t k)
    first := fun t k => D (a.value t k) (a.first t k)
    second := fun t k => H (a.value t k) (a.first t k) (a.first t k)+D (a.value t k) (a.second t k)
    deriv_value := fun t k => (hdG _).comp_hasDerivAt t (a.deriv_value t k)
    deriv_first := fun t k => ((hdD _).comp_hasDerivAt t (a.deriv_value t k)).clm_apply (a.deriv_first t k)
    measurable_value := fun t => hG.continuous.comp_aestronglyMeasurable (a.measurable_value t)
    measurable_first := ?_
    measurable_second := ?_
    gaussian_bound := ?_ }
  · have hd : Continuous (fun z : E×E => D z.1 z.2) := (hDc.comp continuous_fst).clm_apply continuous_snd
    exact fun t => hd.comp_aestronglyMeasurable ((a.measurable_value t).prodMk (a.measurable_first t))
  · have hd : Continuous (fun z : E×E => D z.1 z.2) := (hDc.comp continuous_fst).clm_apply continuous_snd
    have hh : Continuous (fun z : E×E => H z.1 z.2 z.2) := ((hHc.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
    exact fun t => (hh.comp_aestronglyMeasurable ((a.measurable_value t).prodMk (a.measurable_first t))).add
      (hd.comp_aestronglyMeasurable ((a.measurable_value t).prodMk (a.measurable_second t)))
  · obtain ⟨C,hC,hc⟩ := a.gaussian_bound
    let K := closedBall (0:E) C
    obtain ⟨B,hB⟩ := (isCompact_closedBall (0:E) C).bddAbove_image hDc.norm.continuousOn
    have hh : Continuous (fun z : E×E => H z.1 z.2) := (hHc.comp continuous_fst).clm_apply continuous_snd
    obtain ⟨A,hA⟩ := ((isCompact_closedBall (0:E) C).prod (isCompact_closedBall (0:E) C)).bddAbove_image hh.norm.continuousOn
    have hz : (0:E)∈K := mem_closedBall_self hC
    have bn : 0≤B := (norm_nonneg (D 0)).trans (hB ⟨_,hz,rfl⟩)
    have an : 0≤A := (norm_nonneg (H 0 0)).trans (hA ⟨(0,0),⟨hz,hz⟩,rfl⟩)
    refine ⟨B*C+A*C,by positivity,?_⟩
    intro t k ht
    obtain ⟨hv,hf,hs⟩ := hc t k ht
    have hk : a.value t k∈K := by
      rw [show K=closedBall (0:E) C from rfl,mem_closedBall_zero_iff]
      exact hv.trans (mul_le_of_le_one_right hC (heat_loop_majorant_le_one k))
    have hr : ‖a.first t k‖≤C := hf.trans (mul_le_of_le_one_right hC (heat_loop_majorant_le_one k))
    have db : ∀ z∈K, ‖D z‖≤B := fun z h => hB ⟨z,h,rfl⟩
    have hfk : a.first t k∈K := mem_closedBall_zero_iff.mpr hr
    have ab : ‖H (a.value t k) (a.first t k)‖≤A := hA ⟨(a.value t k,a.first t k),⟨hk,hfk⟩,rfl⟩
    have nM := Real.exp_nonneg (-‖k‖^2/4)
    change 0≤heatLoopMajorant k at nM
    have base : B*C*heatLoopMajorant k≤(B*C+A*C)*heatLoopMajorant k := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg an hC)) nM
    constructor
    · have h := (convex_closedBall (0:E) C).norm_image_sub_le_of_norm_fderiv_le
        (fun _ _ => (hdG _).differentiableAt) db hz hk
      rw [h0,sub_zero,sub_zero] at h
      exact (h.trans (mul_le_mul_of_nonneg_left hv bn)).trans ((mul_assoc _ _ _).symm.le.trans base)
    constructor
    · exact (((D _).le_opNorm _).trans (mul_le_mul (db _ hk) hf (norm_nonneg _) bn)).trans
        ((mul_assoc _ _ _).symm.le.trans base)
    · refine (norm_add_le _ _).trans ?_
      have j1 := ((H (a.value t k) (a.first t k)).le_opNorm (a.first t k)).trans
        (mul_le_mul ab hf (norm_nonneg _) an)
      have j2 := ((D (a.value t k)).le_opNorm (a.second t k)).trans (mul_le_mul (db _ hk) hs (norm_nonneg _) bn)
      linarith [show A*(C*heatLoopMajorant k)+B*(C*heatLoopMajorant k)=(B*C+A*C)*heatLoopMajorant k by ring]

theorem heat_loop_integral_local_derivatives (a : HeatLoopCurve ℝ) :
    (∀ t : ℝ, |t|<1 → HasDerivAt (fun s => ∫ k, a.value s k) (∫ k, a.first t k) t) ∧
      HasDerivAt (fun s => ∫ k, a.first s k) (∫ k, a.second 0 k) 0 := by
  obtain ⟨C,hC,hb⟩ := a.gaussian_bound
  have hi : Integrable (fun k => C*heatLoopMajorant k) := heat_loop_majorant_integrable.const_mul C
  have hb' {s t : ℝ} (ht : |t|<1) (hs : s∈ball t (1-|t|)) : |s|≤1 := by
    have hu := abs_add_le (s-t) t
    rw [sub_add_cancel] at hu
    rw [mem_ball,Real.dist_eq] at hs
    linarith
  have hval {t : ℝ} (ht : |t|<1) : HasDerivAt (fun s => ∫ k, a.value s k) (∫ k, a.first t k) t :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=a.value) (F':=a.first) (μ:=volume) (sub_pos.mpr ht)
      (Eventually.of_forall a.measurable_value) (hi.mono' (a.measurable_value t) (Eventually.of_forall fun k => (hb _ _ ht.le).1))
      (a.measurable_first t) (Eventually.of_forall fun k s hs => (hb _ _ (hb' ht hs)).2.1) hi
      (Eventually.of_forall fun k s _ => a.deriv_value s k)).2
  have hz : |(0:ℝ)| < 1 := by norm_num
  have hfirst := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=a.first) (F':=a.second) (μ:=volume) (sub_pos.mpr hz)
    (Eventually.of_forall a.measurable_first) (hi.mono' (a.measurable_first 0) (Eventually.of_forall fun k => (hb _ _ hz.le).2.1))
    (a.measurable_second 0) (Eventually.of_forall fun k s hs => (hb _ _ (hb' hz hs)).2.2) hi
    (Eventually.of_forall fun k s _ => a.deriv_first s k)).2
  exact ⟨fun _ ht => hval ht,hfirst⟩

theorem heat_loop_integral_second (a : HeatLoopCurve ℝ) :
    deriv (deriv (fun t => ∫ k, a.value t k)) 0 = ∫ k, a.second 0 k := by
  obtain ⟨hval,hfirst⟩ := heat_loop_integral_local_derivatives a
  have hz : |(0:ℝ)| < 1 := by norm_num
  apply Eq.trans _ hfirst.deriv
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [(continuous_abs.continuousAt (x:=(0:ℝ))).eventually_lt continuousAt_const hz] with t ht
  exact (hval t ht).deriv

end UV.HeatMaxwell
