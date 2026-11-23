import UV.ContinueRadialPhotonConcentration

/-! Precision and inverse-form bounds on a symmetric Euclidean time slab.
The variational covariance uses the full real-line Sobolev form domain
with its locally absolutely continuous representatives. -/

noncomputable section

namespace UV.RadialPhoton

open MeasureTheory Filter Set Real
open scoped Topology RealInnerProductSpace

structure TimeFormProfile where
  value : ℝ → ℝ
  slope : ℝ → ℝ
  value_L2 : MemLp value 2 volume
  slope_L2 : MemLp slope 2 volume
  primitive : ∀ l r, value r - value l = ∫ t in l..r, slope t

instance : Nonempty TimeFormProfile := ⟨{
  value := 0, slope := 0, value_L2 := MemLp.zero, slope_L2 := MemLp.zero,
  primitive := by simp }⟩

def slabPrecision (e k T : ℝ) (depth : ℝ → ℝ) (t : ℝ) : ℝ :=
  k^2 + (Icc (-T) T).indicator (fun u => e^2*k^2*(depthDifference (depth u) k)^2) t

/-- Spatial magnetic energy of the routed transverse unit polarization,
with the actual time-dependent readout at both ends. -/
theorem slab_precision_transverse_mode (n u : SectorPlane.UnitVector SectorPlane.Spatial)
    (hu : inner ℝ n.val u.val = 0) (e k T t A : ℝ) (depth : ℝ → ℝ) :
    let B := (Icc (-T) T).indicator (fun q => e^2*(depthDifference (depth q) k)^2) t
    SectorPlane.spatialCurvatureNormSq (k • n.val) (A • u.val) +
      B*SectorPlane.spatialCurvatureNormSq (k • n.val) (A • u.val) =
      slabPrecision e k T depth t*A^2 := by
  have h : SectorPlane.spatialCurvatureNormSq (k • n.val) (A • u.val) = k^2*A^2 := by
    simpa only [zero_mul,zero_add,one_mul,add_zero] using
      SectorPlane.transverse_normal_energy_density n u hu k 0 A 0 0 1 0
  intro B
  rw [h]
  by_cases ht : t ∈ Icc (-T) T
  · simp [B,slabPrecision,ht]
    ring
  · simp [B,slabPrecision,ht]

theorem slab_precision_bounds {e k R T : ℝ} {depth : ℝ → ℝ} (hk : 0 ≤ k) (hR : 0 ≤ R)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc (-T) T → depth t ∈ Icc 0 R) :
    ∀ᵐ t ∂(volume : Measure ℝ), slabPrecision e k T depth t ∈
      Icc (k^2) ((1+e^2*depthDelta R k)*k^2) := by
  have hδ : 0 ≤ depthDelta R k := (depth_difference_bounds (r := 0) le_rfl hR hk).2.2.trans'
    (sq_nonneg _)
  filter_upwards [hd] with t ht
  by_cases hm : t ∈ Icc (-T) T
  · rw [slabPrecision,indicator_of_mem hm]
    have h := (depth_difference_bounds (ht hm).1 (ht hm).2 hk).2.2
    have hb := mul_le_mul_of_nonneg_left h (mul_nonneg (sq_nonneg e) (sq_nonneg k))
    exact ⟨le_add_of_nonneg_right (by positivity),by nlinarith only [hb]⟩
  · rw [slabPrecision,indicator_of_notMem hm,add_zero]
    exact ⟨le_rfl,by nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg e) hδ) (sq_nonneg k)]⟩

theorem slab_precision_measurable {depth : ℝ → ℝ} (hd : AEMeasurable depth volume) (e k T : ℝ) :
    AEMeasurable (slabPrecision e k T depth) volume := by
  have hf : AEMeasurable (fun u => e^2*k^2*(depthDifference (depth u) k)^2) volume := by
    unfold depthDifference
    fun_prop
  exact aemeasurable_const.add (hf.indicator measurableSet_Icc)

def timeProbeAction (B j : ℝ → ℝ) (v : TimeFormProfile) : ℝ :=
  ∫ t, 2*(j t*v.value t) - ((v.slope t)^2+B t*(v.value t)^2)

def timeProbeCovariance (B j : ℝ → ℝ) : ℝ := ⨆ v : TimeFormProfile, timeProbeAction B j v

private theorem action_integrable {B j : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hB : AEMeasurable B volume) (hb : ∀ᵐ t ∂volume, B t ∈ Icc a b)
    (hj : MemLp j 2 volume) (v : TimeFormProfile) :
    Integrable (fun t => 2*(j t*v.value t)-((v.slope t)^2+B t*(v.value t)^2)) := by
  have h : ∀ᵐ t ∂volume, ‖B t‖ ≤ b := hb.mono fun t ht =>
    by simpa only [Real.norm_of_nonneg (ha.trans ht.1)] using ht.2
  exact ((hj.integrable_mul v.value_L2).const_mul 2).sub (v.slope_L2.integrable_sq.add
    (v.value_L2.integrable_sq.bdd_mul' hB.aestronglyMeasurable h))

private theorem time_action_le {B j : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hB : AEMeasurable B volume) (hb : ∀ᵐ t ∂volume, B t ∈ Icc a b) (hj : MemLp j 2 volume)
    (v : TimeFormProfile) : timeProbeAction B j v ≤ ∫ t, (j t)^2/a := by
  apply integral_mono_ae (action_integrable ha.le hB hb hj v) (hj.integrable_sq.div_const a)
  filter_upwards [hb] with t ht
  have hbound := mul_le_mul_of_nonneg_right ht.1 (sq_nonneg (v.value t))
  apply (le_div_iff₀ ha).mpr
  nlinarith only [sq_nonneg (j t-a*v.value t),mul_nonneg ha.le (sq_nonneg (v.slope t)),
    mul_le_mul_of_nonneg_left hbound ha.le]

private theorem actions_bounded {B j : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hB : AEMeasurable B volume) (hb : ∀ᵐ t ∂volume, B t ∈ Icc a b) (hj : MemLp j 2 volume) :
    BddAbove (range (timeProbeAction B j)) :=
  ⟨∫ t, (j t)^2/a,fun _ ⟨v,hv⟩ => hv ▸ time_action_le ha hB hb hj v⟩

theorem free_time_probe_covariance_le {j : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hj : MemLp j 2 volume) :
    timeProbeCovariance (fun _ => a) j ≤ (∫ t, (j t)^2)/a := by
  rw [← integral_div]
  exact ciSup_le (time_action_le ha aemeasurable_const (b := a)
    (Eventually.of_forall fun _ => ⟨le_rfl,le_rfl⟩) hj)

/-- Inverse order for every square-integrable time probe on each admissible path. -/
theorem slab_probe_covariance_sandwich {depth j : ℝ → ℝ} {e k R T : ℝ}
    (hk : 0 < k) (hR : 0 ≤ R) (hd : AEMeasurable depth volume)
    (hr : ∀ᵐ t ∂volume, t ∈ Icc (-T) T → depth t ∈ Icc 0 R) (hj : MemLp j 2 volume) :
    timeProbeCovariance (slabPrecision e k T depth) j ∈
      Icc (timeProbeCovariance (fun _ => (1+e^2*depthDelta R k)*k^2) j)
        (timeProbeCovariance (fun _ => k^2) j) := by
  let a := k^2
  let b := (1+e^2*depthDelta R k)*k^2
  let B := slabPrecision e k T depth
  have ha : 0 < a := sq_pos_of_pos hk
  have hδ : 0 ≤ depthDelta R k := le_min zero_le_one (by positivity)
  have hab : a ≤ b := by
    dsimp [a,b]
    nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg e) hδ) (sq_nonneg k)]
  have hB : AEMeasurable B volume := slab_precision_measurable hd e k T
  have hb : ∀ᵐ t ∂volume, B t ∈ Icc a b := slab_precision_bounds hk.le hR hr
  have hlow : ∀ᵐ _ : ℝ ∂volume, a ∈ Icc a b := Eventually.of_forall fun _ => ⟨le_rfl,hab⟩
  have hhigh : ∀ᵐ _ : ℝ ∂volume, b ∈ Icc a b := Eventually.of_forall fun _ => ⟨hab,le_rfl⟩
  constructor
  · apply ciSup_mono (actions_bounded ha hB hb hj)
    intro v
    apply integral_mono_ae (action_integrable ha.le aemeasurable_const hhigh hj v)
      (action_integrable ha.le hB hb hj v)
    filter_upwards [hb] with t ht
    linarith only [mul_le_mul_of_nonneg_right ht.2 (sq_nonneg (v.value t))]
  · apply ciSup_mono (actions_bounded ha aemeasurable_const hlow hj)
    intro v
    apply integral_mono_ae (action_integrable ha.le hB hb hj v)
      (action_integrable ha.le aemeasurable_const hlow hj v)
    filter_upwards [hb] with t ht
    linarith only [mul_le_mul_of_nonneg_right ht.1 (sq_nonneg (v.value t))]

/-- The form comparison persists through normalized nonnegative path weights
and through any convergent sequence of those averages. -/
theorem slab_probe_law_limit {Ω : Type*} [MeasurableSpace Ω] (μ : ℕ → Measure Ω)
    [∀ n, IsProbabilityMeasure (μ n)] {j : ℝ → ℝ} {e k R : ℝ} (T : ℕ → ℝ)
    (depth : ℕ → Ω → ℝ → ℝ) (hk : 0 < k) (hR : 0 ≤ R) (hj : MemLp j 2 volume)
    (hd : ∀ n, ∀ᵐ p ∂μ n, AEMeasurable (depth n p) volume ∧
      ∀ᵐ t ∂volume, t ∈ Icc (-(T n)) (T n) → depth n p t ∈ Icc 0 R)
    (hmeas : ∀ n, AEStronglyMeasurable (fun p => timeProbeCovariance
      (slabPrecision e k (T n) (depth n p)) j) (μ n))
    {C : ℝ} (hlim : Tendsto (fun n => ∫ p, timeProbeCovariance
      (slabPrecision e k (T n) (depth n p)) j ∂μ n) atTop (𝓝 C)) :
    C ∈ Icc (timeProbeCovariance (fun _ => (1+e^2*depthDelta R k)*k^2) j)
        (timeProbeCovariance (fun _ => k^2) j) := by
  apply isClosed_Icc.mem_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  let f := fun p => timeProbeCovariance (slabPrecision e k (T n) (depth n p)) j
  let l := timeProbeCovariance (fun _ => (1+e^2*depthDelta R k)*k^2) j
  let u := timeProbeCovariance (fun _ => k^2) j
  have h : ∀ᵐ p ∂μ n, f p ∈ Icc l u := (hd n).mono fun p hp =>
    slab_probe_covariance_sandwich hk hR hp.1 hp.2 hj
  have hi : Integrable f (μ n) := (integrable_const (μ := μ n) (max |l| |u|)).mono'
    (hmeas n) (h.mono fun p hp => by
      rw [Real.norm_eq_abs,abs_le]
      exact ⟨(neg_le_neg (le_max_left |l| |u|)).trans ((neg_abs_le _).trans hp.1),
        hp.2.trans ((le_abs_self _).trans (le_max_right |l| |u|))⟩)
  have h1 := integral_mono_ae (integrable_const (μ := μ n) l) hi (h.mono fun _ hp => hp.1)
  have h2 := integral_mono_ae hi (integrable_const (μ := μ n) u) (h.mono fun _ hp => hp.2)
  simpa only [integral_const,measureReal_univ_eq_one,one_smul] using And.intro h1 h2

end UV.RadialPhoton
