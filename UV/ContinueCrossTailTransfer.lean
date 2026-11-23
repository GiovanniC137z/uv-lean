import UV.ContinueCrossTailMeasure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The bounded error between the hard spectral cutoff and the Stieltjes
weight (x/(x+s)). The atom and fixed low-mass range are included. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UV.RevisionSpectrum

private theorem crossTail_weight_le_one {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) :
    x * stieltjesWeight x s ≤ 1 := by
  rw [stieltjesWeight, ← div_eq_mul_inv, div_le_one (by positivity)]
  linarith

private theorem crossTail_weight_nonneg {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) :
    0 ≤ x * stieltjesWeight x s :=
  mul_nonneg hx.le (stieltjesWeight_pos hx hs).le

private theorem crossTail_weight_cutoff_bound {f : ℝ → ℝ} {B T x : ℝ}
    (hT : 0 < T) (hTx : T ≤ x) (hB : 0 ≤ B)
    (hf : ∀ s, 0 ≤ f s) (hf₀ : ∀ s < 0, f s = 0)
    (hfB : ∀ s > T, f s ≤ B/s)
    (hI : IntegrableOn f (Iic x))
    (hW : Integrable (fun s => f s * stieltjesWeight x s)) :
    |x * (∫ s, f s * stieltjesWeight x s) - (∫ s in Iic x, f s)| ≤
      (∫ s in Iic T, f s) + 2*B := by
  have hx := hT.trans_le hTx
  let W (s : ℝ) := f s * (x * stieltjesWeight x s)
  let E (s : ℝ) := f s - W s
  have hWi : Integrable W := by
    simpa only [W, mul_left_comm _ x] using hW.const_mul x
  have hEi : IntegrableOn E (Iic x) := hI.sub hWi.integrableOn
  have hWpos (s : ℝ) : 0 ≤ W s := by
    by_cases hs : 0 ≤ s
    · exact mul_nonneg (hf _) (crossTail_weight_nonneg hx hs)
    · simp [W, hf₀ s (lt_of_not_ge hs)]
  have hEpos (s : ℝ) : 0 ≤ E s := by
    by_cases hs : 0 ≤ s
    · exact sub_nonneg.mpr (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (crossTail_weight_le_one hx hs) (hf s))
    · simp [E, W, hf₀ s (lt_of_not_ge hs)]
  have heq (s : ℝ) (hs : 0 ≤ s) : E s = f s * (s/(x+s)) := by
    have hz : x+s ≠ 0 := by positivity
    unfold E W stieltjesWeight
    field_simp
    ring
  have hIT := hI.mono_set (Iic_subset_Iic.mpr hTx)
  have hE₁ : (∫ s in Iic T, E s) ≤ ∫ s in Iic T, f s :=
    setIntegral_mono_on (hEi.mono_set (Iic_subset_Iic.mpr hTx)) hIT measurableSet_Iic
      (fun s _ => sub_le_self _ (hWpos s))
  have hE₂ : (∫ s in Ioc T x, E s) ≤ B := by
    have hC : IntegrableOn (fun _ : ℝ => B/x) (Ioc T x) :=
      integrableOn_const measure_Ioc_lt_top.ne
    calc
      _ ≤ ∫ _ in Ioc T x, B/x := by
        apply setIntegral_mono_on (hEi.mono_set Ioc_subset_Iic_self) hC measurableSet_Ioc
        intro s hs
        have hs₀ : 0 < s := hT.trans hs.1
        rw [heq s hs₀.le]
        calc
          _ ≤ (B/s)*(s/(x+s)) :=
            mul_le_mul_of_nonneg_right (hfB s hs.1) (by positivity)
          _ = B/(x+s) := by field_simp
          _ ≤ B/x := div_le_div_of_nonneg_left hB hx (by linarith)
      _ = (x-T)*(B/x) := by
        rw [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul, max_eq_left (sub_nonneg.mpr hTx)]
      _ ≤ x*(B/x) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = B := by field_simp
  have hE₃ : (∫ s in Iic x, E s) ≤ (∫ s in Iic T, f s)+B := by
    rw [← Iic_union_Ioc_eq_Iic hTx,
      setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        (hEi.mono_set (Iic_subset_Iic.mpr hTx)) (hEi.mono_set Ioc_subset_Iic_self)]
    exact add_le_add hE₁ hE₂
  have hW₁ : (∫ s in Ioi x, W s) ≤ B := by
    let G (s : ℝ) := (B*x)*(s ^ (-2 : ℝ))
    have hiG : IntegrableOn G (Ioi x) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx).const_mul (B*x)
    have hG (s : ℝ) (hs : x < s) : W s ≤ G s := by
      have hs₀ : 0 < s := hx.trans hs
      have hweight : x * stieltjesWeight x s ≤ x/s := by
        rw [stieltjesWeight, ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left hx.le hs₀ (by linarith)
      calc
        W s ≤ (B/s)*(x/s) :=
          mul_le_mul (hfB s (hTx.trans_lt hs)) hweight (crossTail_weight_nonneg hx hs₀.le)
            (by positivity)
        _ = G s := by
          dsimp [G]
          rw [show (-2 : ℝ) = -(2:ℕ) by norm_num, Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
          ring
    calc
      _ ≤ ∫ s in Ioi x, G s :=
        setIntegral_mono_on hWi.integrableOn hiG measurableSet_Ioi hG
      _ = B := by
        rw [show G = fun s => (B*x)*(s ^ (-2 : ℝ)) from rfl, integral_const_mul,
          integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx]
        norm_num [Real.rpow_neg_one]
        field_simp
  have hWsplit := integral_add_compl (s := Iic x) measurableSet_Iic hWi
  rw [compl_Iic] at hWsplit
  have hEsplit : (∫ s in Iic x, E s) = (∫ s in Iic x, f s) - (∫ s in Iic x, W s) :=
    integral_sub hI hWi.integrableOn
  have hm : (∫ s, W s) = x * (∫ s, f s * stieltjesWeight x s) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with s
    exact mul_left_comm (f s) x _
  have hEpos' := setIntegral_nonneg (μ := volume) (s := Iic x) measurableSet_Iic (fun s _ => hEpos s)
  have hWpos' := setIntegral_nonneg (μ := volume) (s := Ioi x) measurableSet_Ioi (fun s _ => hWpos s)
  rw [← hm, ← hWsplit, abs_le]
  constructor <;> linarith

/-- At large intrinsic (x), the total variation cutoff mass differs from
(xD_c(x)) by a bounded amount. The continuum uses its literal Stieltjes
weight and the unit atom remains separated from Lebesgue integration. -/
theorem crossTailTransform_cutoff_bound {a M m₂ : ℝ} (ha : 0 < a) (hm₂ : 0 ≤ m₂)
    (hadm : m₂ ≤ M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2)) = 0) :
    ∃ C ≥ 0, ∀ᶠ x : ℝ in atTop,
      |x * crossTailTransform a M m₂ x - (crossTailVariation a M m₂).real (Iic x)| ≤ C := by
  let B := 2*Real.exp (a*M)/Real.pi
  let T := max (M^2+1) (2*m₂)
  let f := crossTailDensity a M m₂
  let r := |verifyCrossResidue a M m₂|
  have hT : 0 < T := (by positivity : 0 < M^2+1).trans_le (le_max_left _ _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hTM : M^2 < T := (by linarith : M^2 < M^2+1).trans_le (le_max_left _ _)
  refine ⟨r+(∫ s in Iic T, f s)+2*B, ?_, ?_⟩
  · exact add_nonneg (add_nonneg (abs_nonneg _)
      (setIntegral_nonneg measurableSet_Iic (fun s _ => crossTailDensity_nonneg a M m₂ s)))
      (mul_nonneg (by norm_num) hB)
  filter_upwards [eventually_ge_atTop T] with x hx
  have hx₀ := hT.trans_le hx
  have hmx : m₂ ≤ x := (by linarith [hm₂, (le_max_right (M^2+1) (2*m₂))] : m₂ ≤ T).trans hx
  have hcont := crossTail_weight_cutoff_bound hT hx hB (crossTailDensity_nonneg a M m₂)
    (fun s hs => crossTailDensity_zero_below (hs.le.trans (sq_nonneg M)))
    (fun s hs => crossTailDensity_large_bound (hT.trans hs) (hTM.trans hs)
      ((le_max_right (M^2+1) (2*m₂)).trans (le_of_lt hs)))
    (crossTailDensity_integrableOn_Iic ha hm₂ hadm x)
    (crossTailDensity_weight_integrable ha hm₂ hx₀ hadm)
  have hr : |x*(r*stieltjesWeight x m₂)-r| ≤ r := by
    have hp := crossTail_weight_nonneg hx₀ hm₂
    have hq := crossTail_weight_le_one hx₀ hm₂
    rw [mul_left_comm x r, abs_le]
    constructor <;> nlinarith [abs_nonneg (verifyCrossResidue a M m₂),
      mul_nonneg (show 0 ≤ r from abs_nonneg _) hp,
      mul_nonneg (show 0 ≤ r from abs_nonneg _) (sub_nonneg.mpr hq)]
  rw [crossTailTransform_eq ha hm₂ hx₀ hadm, crossTailVariation_cutoff_eq ha hm₂ hadm hmx]
  change |x * (r * stieltjesWeight x m₂ + ∫ s, f s * stieltjesWeight x s) -
    (r + ∫ s in Iic x, f s)| ≤ _
  rw [mul_add, add_sub_add_comm]
  exact (abs_add_le _ _).trans (by linarith)

end UV.RevisionSpectrum
