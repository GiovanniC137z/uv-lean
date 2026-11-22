import UV.ResumeStableCone
import UV.ExtendTransverseChart

/-! Positive-mass coarea coordinates for the two real axial sheets.
The normal test is cut off in a band lying entirely inside the timelike
region, and the transverse measure remains ordinary spatial volume. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set
open scoped NNReal Topology

/-- A Lipschitz normal cutoff, equal to one at the shell. -/
def massiveNormalCutoff (b D : ℝ) : ℝ := max 0 (1 - |D| * b⁻¹)

theorem massive_normal_cutoff_nonneg (b D : ℝ) : 0 ≤ massiveNormalCutoff b D :=
  le_max_left _ _

theorem massive_normal_cutoff_le_one {b : ℝ} (hb : 0 < b) (D : ℝ) :
    massiveNormalCutoff b D ≤ 1 := by
  unfold massiveNormalCutoff
  exact max_le zero_le_one (sub_le_self _ (mul_nonneg (abs_nonneg _) (inv_nonneg.mpr hb.le)))

theorem massive_normal_cutoff_zero {b D : ℝ} (hb : 0 < b) (hD : b ≤ |D|) :
    massiveNormalCutoff b D = 0 := by
  unfold massiveNormalCutoff
  apply max_eq_left
  have h : 1 ≤ |D| * b⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hb, one_mul]
    exact hD
  linarith

theorem massive_normal_cutoff_lipschitz {b : ℝ} (hb : 0 < b) :
    LipschitzWith ⟨b⁻¹, inv_nonneg.mpr hb.le⟩ (massiveNormalCutoff b) := by
  have h : LipschitzWith ⟨b⁻¹, inv_nonneg.mpr hb.le⟩
      (fun D : ℝ => 1 - |D| * b⁻¹) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |(1 - |x| * b⁻¹) - (1 - |y| * b⁻¹)| ≤ b⁻¹ * |x - y|
    rw [show (1 - |x| * b⁻¹) - (1 - |y| * b⁻¹) = (|y| - |x|) * b⁻¹ by ring,
      abs_mul, abs_of_nonneg (inv_nonneg.mpr hb.le), abs_sub_comm |y| |x|, mul_comm b⁻¹]
    exact mul_le_mul_of_nonneg_right (abs_abs_sub_abs_le_abs_sub x y) (inv_nonneg.mpr hb.le)
  exact h.const_max 0

/-- A globally regular extension of the positive axial square root
from the compact support of the normal cutoff. -/
def massiveChartRoot (b m D : ℝ) (p : Spatial) : ℝ :=
  Real.sqrt (max b (D + shellFrequency m p ^ 2))

theorem massive_chart_root_le_lower {b : ℝ} (hb : 0 < b) (m D : ℝ) (p : Spatial) :
    0 < Real.sqrt b ∧ Real.sqrt b ≤ massiveChartRoot b m D p :=
  ⟨Real.sqrt_pos.mpr hb, Real.sqrt_le_sqrt (le_max_left _ _)⟩

private theorem massive_chart_root_lipschitz {b : ℝ} (hb : 0 < b) (m : ℝ) (p : Spatial) :
    let r := (2 * Real.sqrt b)⁻¹
    LipschitzWith ⟨r, inv_nonneg.mpr (by positivity)⟩ (fun D => massiveChartRoot b m D p) := by
  dsimp only
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let u := max b (x + shellFrequency m p ^ 2)
  let v := max b (y + shellFrequency m p ^ 2)
  let X := Real.sqrt u
  let Y := Real.sqrt v
  have hX : Real.sqrt b ≤ X := Real.sqrt_le_sqrt (le_max_left _ _)
  have hY : Real.sqrt b ≤ Y := Real.sqrt_le_sqrt (le_max_left _ _)
  have hS : 0 < 2 * Real.sqrt b := by positivity
  have hS' : 0 ≤ X + Y := by positivity
  have hv : X ^ 2 = u := Real.sq_sqrt (hb.le.trans (le_max_left _ _))
  have hw : Y ^ 2 = v := Real.sq_sqrt (hb.le.trans (le_max_left _ _))
  have hd : |u - v| ≤ |x - y| := by
    have hA : LipschitzWith 1 (fun z : ℝ => z + shellFrequency m p ^ 2) := by
      apply LipschitzWith.of_dist_le_mul
      intro a c
      rw [NNReal.coe_one, one_mul, dist_add_right]
    have h := hA.const_max b
    simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using h.dist_le_mul x y
  change |X - Y| ≤ (2 * Real.sqrt b)⁻¹ * |x - y|
  rw [inv_mul_eq_div, le_div_iff₀ hS]
  calc
    _ ≤ |X - Y| * (X + Y) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = |u - v| := by
      rw [← abs_of_nonneg hS', ← abs_mul]
      congr 1
      rw [show (X - Y) * (X + Y) = X ^ 2 - Y ^ 2 by ring, hv, hw]
    _ ≤ _ := hd

def massiveChartWeight (b m D : ℝ) (p : Spatial) : ℝ :=
  (2 * massiveChartRoot b m D p)⁻¹

private theorem massive_chart_weight_bound {b : ℝ} (hb : 0 < b) (m D : ℝ) (p : Spatial) :
    ‖massiveChartWeight b m D p‖ ≤ (2 * Real.sqrt b)⁻¹ := by
  obtain ⟨h₁, h₂⟩ := massive_chart_root_le_lower hb m D p
  have hp := h₁.trans_le h₂
  unfold massiveChartWeight
  rw [Real.norm_of_nonneg (by positivity)]
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left h₂ two_pos.le)

private theorem massive_chart_weight_lipschitz {b : ℝ} (hb : 0 < b) (m : ℝ) (p : Spatial) :
    let r := (2 * Real.sqrt b)⁻¹ / (2 * b)
    LipschitzWith ⟨r, by positivity⟩ (fun D => massiveChartWeight b m D p) := by
  dsimp only
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let X := massiveChartRoot b m x p
  let Y := massiveChartRoot b m y p
  obtain ⟨h₁, hx⟩ := massive_chart_root_le_lower hb m x p
  have hy := (massive_chart_root_le_lower hb m y p).2
  have hX := h₁.trans_le hx
  have hY := h₁.trans_le hy
  have hP : 2 * b ≤ 2 * X * Y := by
    have hp := mul_le_mul hx hy h₁.le hX.le
    have hs : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
    nlinarith
  have he : (2 * X)⁻¹ - (2 * Y)⁻¹ = (Y - X) / (2 * X * Y) := by
    have hX' : X ≠ 0 := hX.ne'
    have hY' : Y ≠ 0 := hY.ne'
    field_simp [hX', hY']
  change |(2 * X)⁻¹ - (2 * Y)⁻¹| ≤ ((2 * Real.sqrt b)⁻¹ / (2 * b)) * |x - y|
  rw [he, abs_div, abs_of_pos (by positivity : 0 < 2 * X * Y), abs_sub_comm Y X]
  calc
    _ ≤ |X - Y| / (2 * b) := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hP
    _ ≤ ((2 * Real.sqrt b)⁻¹ * |x - y|) / (2 * b) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hd := (massive_chart_root_lipschitz hb m p).dist_le_mul x y
      simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mk] using hd
    _ = _ := by ring

/-- Sum over both axial sheets with the same genuine coarea factor. -/
def massiveChartTest (b m : ℝ) (f : ℝ × Spatial → ℝ) (q : ℝ × Spatial) : ℝ :=
  massiveNormalCutoff b q.1 * massiveChartWeight b m q.1 q.2 *
    (f (massiveChartRoot b m q.1 q.2, q.2) + f (-massiveChartRoot b m q.1 q.2, q.2))

theorem massive_chart_test_continuous {b m : ℝ} (hb : 0 < b)
    {f : ℝ × Spatial → ℝ} (hf : Continuous f) : Continuous (massiveChartTest b m f) := by
  have hc : Continuous (fun q : ℝ × Spatial => massiveChartRoot b m q.1 q.2) := by
    unfold massiveChartRoot
    simp_rw [shell_frequency_square]
    fun_prop
  have hpos (q : ℝ × Spatial) : 0 < massiveChartRoot b m q.1 q.2 :=
    (massive_chart_root_le_lower hb m q.1 q.2).1.trans_le
      (massive_chart_root_le_lower hb m q.1 q.2).2
  have hw : Continuous (fun q : ℝ × Spatial => massiveChartWeight b m q.1 q.2) :=
    (continuous_const.mul hc).inv₀ (fun q => (mul_pos two_pos (hpos q)).ne')
  have hcut := (massive_normal_cutoff_lipschitz hb).continuous.comp
    (continuous_fst : Continuous (Prod.fst : ℝ × Spatial → ℝ))
  exact (hcut.mul hw).mul
    ((hf.comp (hc.prodMk continuous_snd)).add (hf.comp (hc.neg.prodMk continuous_snd)))

theorem massive_chart_test_bound {b m C : ℝ} (hb : 0 < b)
    {f : ℝ × Spatial → ℝ} (hC : ∀ q, ‖f q‖ ≤ C) (q : ℝ × Spatial) :
    ‖massiveChartTest b m f q‖ ≤ (2 * Real.sqrt b)⁻¹ * (2 * C) := by
  unfold massiveChartTest
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (massive_normal_cutoff_nonneg b q.1)]
  have hf : ‖f (massiveChartRoot b m q.1 q.2, q.2) +
      f (-massiveChartRoot b m q.1 q.2, q.2)‖ ≤ C + C :=
    (norm_add_le _ _).trans (add_le_add (hC _) (hC _))
  have h₁ := mul_le_mul (massive_normal_cutoff_le_one hb q.1)
    (massive_chart_weight_bound hb m q.1 q.2) (norm_nonneg _) zero_le_one
  rw [one_mul] at h₁
  simpa only [two_mul] using mul_le_mul h₁ hf (norm_nonneg _) (by positivity)

private theorem bounded_lipschitz_mul {f g : ℝ → ℝ} {L K C B : ℝ≥0}
    (hf : LipschitzWith L f) (hg : LipschitzWith K g)
    (hC : ∀ x, ‖f x‖ ≤ (C : ℝ)) (hB : ∀ x, ‖g x‖ ≤ (B : ℝ)) :
    LipschitzWith (C * K + B * L) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm, show f x * g x - f y * g y =
    f x * (g x - g y) + g y * (f x - f y) by ring]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul, add_mul]
  exact add_le_add
    (by simpa only [mul_assoc] using mul_le_mul (hC x) (hg.norm_sub_le x y) (norm_nonneg _) C.coe_nonneg)
    (by simpa only [mul_assoc] using mul_le_mul (hB y) (hf.norm_sub_le x y) (norm_nonneg _) B.coe_nonneg)

theorem massive_chart_test_norm_lipschitz {b m : ℝ} (hb : 0 < b)
    {f : ℝ × Spatial → ℝ} {L C : ℝ≥0} (hf : LipschitzWith L f)
    (hC : ∀ q, ‖f q‖ ≤ (C : ℝ)) :
    ∃ K : ℝ≥0, ∀ p : Spatial, LipschitzWith K (fun D => massiveChartTest b m f (D, p)) := by
  let r : ℝ≥0 := ⟨(2 * Real.sqrt b)⁻¹, by positivity⟩
  let t : ℝ≥0 := ⟨(2 * Real.sqrt b)⁻¹ / (2 * b), by positivity⟩
  let s : ℝ≥0 := ⟨b⁻¹, by positivity⟩
  refine ⟨r * (L * r + L * r) + (C + C) * (1 * t + r * s), ?_⟩
  intro p
  have hr : LipschitzWith r (fun D => massiveChartRoot b m D p) :=
    massive_chart_root_lipschitz hb m p
  have hc₁ : LipschitzWith r (fun D => (massiveChartRoot b m D p, p)) := by
    simpa only [max_eq_left (zero_le r), Function.comp_def] using hr.prodMk (LipschitzWith.const p)
  have hc₂ : LipschitzWith r (fun D => (-massiveChartRoot b m D p, p)) := by
    simpa only [max_eq_left (zero_le r), Function.comp_def] using hr.neg.prodMk (LipschitzWith.const p)
  have hpair : LipschitzWith (L * r + L * r)
      (fun D => f (massiveChartRoot b m D p, p) + f (-massiveChartRoot b m D p, p)) :=
    (hf.comp hc₁).add (hf.comp hc₂)
  have hweight : LipschitzWith (1 * t + r * s)
      (fun D => massiveNormalCutoff b D * massiveChartWeight b m D p) :=
    bounded_lipschitz_mul (massive_normal_cutoff_lipschitz hb)
      (massive_chart_weight_lipschitz hb m p)
      (fun D => by simpa only [Real.norm_of_nonneg (massive_normal_cutoff_nonneg b D), NNReal.coe_one]
        using massive_normal_cutoff_le_one hb D)
      (fun D => massive_chart_weight_bound hb m D p)
  exact bounded_lipschitz_mul hweight hpair
    (fun D => by
      rw [norm_mul, Real.norm_of_nonneg (massive_normal_cutoff_nonneg b D)]
      exact (mul_le_mul (massive_normal_cutoff_le_one hb D) (massive_chart_weight_bound hb m D p)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    (fun D => by
      rw [NNReal.coe_add]
      exact (norm_add_le _ _).trans (add_le_add (hC _) (hC _)))

end UV.SectorPlane
