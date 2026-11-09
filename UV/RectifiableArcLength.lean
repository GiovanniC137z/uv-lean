import UV.RectifiableContourParameter
import Mathlib.Topology.Semicontinuous

/-! Continuous rectifiable curves admit the actual full arc-length interval.
Continuity of cumulative variation is proved from lower semicontinuity of
the two complementary clamped curves and exact additivity of variation. -/

noncomputable section
open Set Filter
open scoped Topology ENNReal NNReal

namespace UV

/-- Finite extended variation is lower semicontinuous under pointwise
continuous dependence of the curve on a parameter. -/
theorem finite_variation_lowerSemicontinuousOn
    {T : Type*} [TopologicalSpace T] {E : Type*} [PseudoEMetricSpace E]
    {F : T → ℝ → E} {s : Set ℝ} {t : Set T}
    (hfinite : ∀ u ∈ t, BoundedVariationOn (F u) s)
    (hcont : ∀ x ∈ s, ContinuousOn (fun u => F u x) t) :
    LowerSemicontinuousOn (fun u => (eVariationOn (F u) s).toReal) t := by
  intro u hu v hv
  by_cases hvneg : v < 0
  · exact Eventually.of_forall (fun _ => hvneg.trans_le ENNReal.toReal_nonneg)
  have hv0 : 0 ≤ v := le_of_not_gt hvneg
  have hve : ENNReal.ofReal v < eVariationOn (F u) s :=
    (ENNReal.ofReal_lt_iff_lt_toReal hv0 (hfinite u hu)).mpr hv
  have hev := eVariationOn.lowerSemicontinuous_aux
    (F := F) (f := F u) (p := 𝓝[t] u)
    (fun x hx => hcont x hx u hu) hve
  filter_upwards [hev, self_mem_nhdsWithin] with w hw hwt
  exact (ENNReal.ofReal_lt_iff_lt_toReal hv0 (hfinite w hwt)).mp hw

theorem interval_image_min {a b u : ℝ} (hu : u ∈ Icc a b) :
    (fun x : ℝ => min x u) '' Icc a b = Icc a u := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨le_min hx.1 hu.1, min_le_right _ _⟩
  · intro hy
    exact ⟨y, ⟨hy.1, hy.2.trans hu.2⟩, min_eq_left hy.2⟩

theorem interval_image_max {a b u : ℝ} (hu : u ∈ Icc a b) :
    (fun x : ℝ => max x u) '' Icc a b = Icc u b := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨le_max_right _ _, max_le hx.2 hu.2⟩
  · intro hy
    exact ⟨y, ⟨hu.1.trans hy.1, hy.2⟩, max_eq_left hy.1⟩

theorem clamped_min_variation {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ → E) {a b u : ℝ} (hu : u ∈ Icc a b) :
    eVariationOn (fun x => f (min x u)) (Icc a b) = eVariationOn f (Icc a u) := by
  have h := eVariationOn.comp_eq_of_monotoneOn f (fun x : ℝ => min x u)
    (fun _ _ _ _ hxy => min_le_min hxy le_rfl : MonotoneOn (fun x => min x u) (Icc a b))
  simpa only [Function.comp_def, interval_image_min hu] using h

theorem clamped_max_variation {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ → E) {a b u : ℝ} (hu : u ∈ Icc a b) :
    eVariationOn (fun x => f (max x u)) (Icc a b) = eVariationOn f (Icc u b) := by
  have h := eVariationOn.comp_eq_of_monotoneOn f (fun x : ℝ => max x u)
    (fun _ _ _ _ hxy => max_le_max hxy le_rfl : MonotoneOn (fun x => max x u) (Icc a b))
  simpa only [Function.comp_def, interval_image_max hu] using h

/-- A continuous bounded-variation curve has continuous cumulative
variation, including both endpoints of the original interval. -/
theorem rectifiable_variation_continuousOn {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {a b : ℝ}
    (hBV : BoundedVariationOn f (Icc a b)) (hf : ContinuousOn f (Icc a b)) :
    ContinuousOn (variationOnFromTo f (Icc a b) a) (Icc a b) := by
  let V : ℝ → ℝ := fun u => (eVariationOn (fun x => f (min x u)) (Icc a b)).toReal
  let W : ℝ → ℝ := fun u => (eVariationOn (fun x => f (max x u)) (Icc a b)).toReal
  have hVfinite : ∀ u ∈ Icc a b,
      BoundedVariationOn (fun x => f (min x u)) (Icc a b) := by
    intro u hu
    change eVariationOn (fun x => f (min x u)) (Icc a b) ≠ ∞
    rw [clamped_min_variation f hu]
    exact hBV.mono (Icc_subset_Icc le_rfl hu.2)
  have hWfinite : ∀ u ∈ Icc a b,
      BoundedVariationOn (fun x => f (max x u)) (Icc a b) := by
    intro u hu
    change eVariationOn (fun x => f (max x u)) (Icc a b) ≠ ∞
    rw [clamped_max_variation f hu]
    exact hBV.mono (Icc_subset_Icc hu.1 le_rfl)
  have hVcont : ∀ x ∈ Icc a b, ContinuousOn (fun u => f (min x u)) (Icc a b) := by
    intro x hx
    apply hf.comp (continuous_const.min continuous_id).continuousOn
    intro u hu
    exact ⟨le_min hx.1 hu.1, (min_le_left _ _).trans hx.2⟩
  have hWcont : ∀ x ∈ Icc a b, ContinuousOn (fun u => f (max x u)) (Icc a b) := by
    intro x hx
    apply hf.comp (continuous_const.max continuous_id).continuousOn
    intro u hu
    exact ⟨hx.1.trans (le_max_left _ _), max_le hx.2 hu.2⟩
  have hVl : LowerSemicontinuousOn V (Icc a b) :=
    finite_variation_lowerSemicontinuousOn hVfinite hVcont
  have hWl : LowerSemicontinuousOn W (Icc a b) :=
    finite_variation_lowerSemicontinuousOn hWfinite hWcont
  have hsum : ∀ u ∈ Icc a b, V u + W u = (eVariationOn f (Icc a b)).toReal := by
    intro u hu
    dsimp only [V, W]
    rw [clamped_min_variation f hu, clamped_max_variation f hu,
      ← ENNReal.toReal_add (hBV.mono (Icc_subset_Icc le_rfl hu.2))
        (hBV.mono (Icc_subset_Icc hu.1 le_rfl))]
    congr 1
    simpa only [univ_inter] using
      (eVariationOn.Icc_add_Icc f (s := univ) hu.1 hu.2 (mem_univ u))
  have hVu : UpperSemicontinuousOn V (Icc a b) := by
    intro u hu v hv
    have hcut : (eVariationOn f (Icc a b)).toReal-v < W u := by
      have hs := hsum u hu
      linarith
    filter_upwards [hWl u hu _ hcut, self_mem_nhdsWithin] with w hw hwt
    have hs := hsum w hwt
    linarith
  have hVc : ContinuousOn V (Icc a b) :=
    continuousOn_iff_lower_upperSemicontinuousOn.mpr ⟨hVl, hVu⟩
  apply hVc.congr
  intro u hu
  rw [variationOnFromTo.eq_of_le f (Icc a b) hu.1,
    inter_eq_right.mpr (Icc_subset_Icc le_rfl hu.2)]
  exact congrArg ENNReal.toReal (clamped_min_variation f hu).symm

/-- A continuous rectifiable curve has its actual entire arc-length interval
as parameter domain. It is reconstructed through an increasing continuous
variation parameter; the unit-speed representative preserves endpoints,
oriented traversal, geometric image and exact total variation. -/
theorem continuous_rectifiable_arcLength_factorization {E : Type*} [EMetricSpace E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hBV : BoundedVariationOn f (Icc a b)) (hf : ContinuousOn f (Icc a b)) :
    let L := (eVariationOn f (Icc a b)).toReal
    let v := variationOnFromTo f (Icc a b) a
    let g := naturalParameterization f (Icc a b) a
    0 ≤ L ∧ ContinuousOn v (Icc a b) ∧ MonotoneOn v (Icc a b) ∧
      v '' Icc a b = Icc 0 L ∧ HasUnitSpeedOn g (Icc 0 L) ∧
      LipschitzOnWith 1 g (Icc 0 L) ∧
      (∀ t ∈ Icc a b, g (v t) = f t) ∧
      g 0 = f a ∧ g L = f b ∧ g '' Icc 0 L = f '' Icc a b ∧
      eVariationOn g (Icc 0 L) = ENNReal.ofReal L := by
  let L := (eVariationOn f (Icc a b)).toReal
  let v := variationOnFromTo f (Icc a b) a
  let g := naturalParameterization f (Icc a b) a
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hlbv := hBV.locallyBoundedVariationOn
  have hvc := rectifiable_variation_continuousOn hBV hf
  have hvb : variationOnFromTo f (Icc a b) a b = L := by
    rw [variationOnFromTo.eq_of_le f (Icc a b) hab, inter_self]
  have hvi : v '' Icc a b = Icc 0 L := by
    simpa only [hvb] using rectifiable_variation_image_interval hab hlbv hvc
  have hu : HasUnitSpeedOn g (Icc 0 L) := by
    rw [← hvi]
    exact has_unit_speed_naturalParameterization f hlbv ha
  have hr : ∀ t ∈ Icc a b, g (v t) = f t :=
    fun t ht => naturalParameterization_reconstruct hlbv ha ht
  have hleft : g 0 = f a := by
    simpa only [v, variationOnFromTo.self] using hr a ha
  have hright : g L = f b := by
    have h := hr b hb
    have hvb' : v b = L := hvb
    rwa [hvb'] at h
  have himg : g '' Icc 0 L = f '' Icc a b := by
    rw [← hvi, ← image_comp]
    exact image_congr hr
  have htotal : eVariationOn g (Icc 0 L) = ENNReal.ofReal L := by
    simpa only [inter_self, NNReal.coe_one, one_mul, sub_zero] using
      hu (x := 0) (y := L) ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩
  exact ⟨hL, hvc, variationOnFromTo.monotoneOn hlbv ha, hvi, hu,
    unitSpeed_lipschitzOn hu, hr, hleft, hright, himg, htotal⟩

end UV
