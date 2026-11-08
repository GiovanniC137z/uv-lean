import UV.GaussianBoundaryGrowth
import UV.LogPotential

/-! Growth of the genuine standard-bubble upper-rim boundary. Its quadratic
roots yield two actual translated logarithmic potentials on [0,1]. -/

noncomputable section
open MeasureTheory Set Real Filter
open scoped Topology

namespace UV

def standardBoundaryBeta (m s : ℝ) : ℝ := Real.sqrt (1 - 4 * m ^ 2 / s)
def standardBoundaryRootMinus (m s : ℝ) : ℝ := (1 - standardBoundaryBeta m s) / 2
def standardBoundaryRootPlus (m s : ℝ) : ℝ := (1 + standardBoundaryBeta m s) / 2

theorem standard_boundary_beta_bounds {m s : ℝ} (hm : 0 < m) (hs : 4 * m ^ 2 < s) :
    0 ≤ standardBoundaryBeta m s ∧ standardBoundaryBeta m s ≤ 1 ∧
      s * (standardBoundaryBeta m s) ^ 2 = s - 4 * m ^ 2 := by
  have hspos : 0 < s := lt_trans (by positivity) hs
  have hδ : 0 ≤ 1 - 4 * m ^ 2 / s := by
    exact sub_nonneg.mpr ((div_le_one hspos).mpr hs.le)
  have hδ1 : 1 - 4 * m ^ 2 / s ≤ 1 := sub_le_self _ (by positivity)
  have hnonneg : 0 ≤ standardBoundaryBeta m s := Real.sqrt_nonneg _
  have hsq : (standardBoundaryBeta m s) ^ 2 = 1 - 4 * m ^ 2 / s := Real.sq_sqrt hδ
  refine ⟨hnonneg, ?_, ?_⟩
  · nlinarith
  · rw [hsq]
    field_simp

theorem standard_boundary_roots_mem {m s : ℝ} (hm : 0 < m) (hs : 4 * m ^ 2 < s) :
    standardBoundaryRootMinus m s ∈ Icc (0 : ℝ) 1 ∧
      standardBoundaryRootPlus m s ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h₀, h₁, _⟩ := standard_boundary_beta_bounds hm hs
  unfold standardBoundaryRootMinus standardBoundaryRootPlus
  constructor <;> constructor <;> linarith

theorem standard_boundary_denominator_factor {m s : ℝ} (hm : 0 < m)
    (hs : 4 * m ^ 2 < s) (x : ℝ) :
    standardBubbleRealDenominator m s x =
      s * (x - standardBoundaryRootMinus m s) * (x - standardBoundaryRootPlus m s) := by
  obtain ⟨_, _, he⟩ := standard_boundary_beta_bounds hm hs
  unfold standardBubbleRealDenominator bubbleFeynmanWeight standardBoundaryRootMinus standardBoundaryRootPlus
  nlinarith

theorem standard_boundary_log_factorization_ae {m s : ℝ} (hm : 0 < m)
    (hs : 4 * m ^ 2 < s) :
    (fun x => Real.log (standardBubbleRealDenominator m s x)) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      (fun x => Real.log s + Real.log (x - standardBoundaryRootMinus m s) +
        Real.log (x - standardBoundaryRootPlus m s)) := by
  have hspos : 0 < s := lt_trans (by positivity) hs
  have hminus : ∀ᵐ x : ℝ ∂volume.restrict (Icc (0 : ℝ) 1), x ≠ standardBoundaryRootMinus m s := by
    rw [ae_iff]
    simp
  have hplus : ∀ᵐ x : ℝ ∂volume.restrict (Icc (0 : ℝ) 1), x ≠ standardBoundaryRootPlus m s := by
    rw [ae_iff]
    simp
  filter_upwards [hminus, hplus] with x hmroot hproot
  rw [standard_boundary_denominator_factor hm hs x,
    Real.log_mul (mul_ne_zero hspos.ne' (sub_ne_zero.mpr hmroot)) (sub_ne_zero.mpr hproot),
    Real.log_mul hspos.ne' (sub_ne_zero.mpr hmroot)]

theorem standard_boundary_denominator_abs_log_bound {m s : ℝ} (hm : 0 < m)
    (hs : 4 * m ^ 2 < s) :
    (∫ x in Icc (0 : ℝ) 1, |Real.log (standardBubbleRealDenominator m s x)|) ≤ |Real.log s| + 6 := by
  have hminus := translated_log_abs_integrable (standardBoundaryRootMinus m s)
  have hplus := translated_log_abs_integrable (standardBoundaryRootPlus m s)
  have hmajor : IntegrableOn (fun x : ℝ => |Real.log s| +
      |Real.log (x - standardBoundaryRootMinus m s)| + |Real.log (x - standardBoundaryRootPlus m s)|)
      (Icc (0 : ℝ) 1) := ((integrable_const _).add hminus).add hplus
  have hbound := integral_mono_ae (standard_bubble_denominator_log_integrable m s) hmajor
    (by
      filter_upwards [standard_boundary_log_factorization_ae hm hs] with x hx
      rw [hx]
      exact (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _))
  rw [integral_add (f := fun x : ℝ => |Real.log s| + |Real.log (x - standardBoundaryRootMinus m s)|)
      (g := fun x : ℝ => |Real.log (x - standardBoundaryRootPlus m s)|)
      ((integrable_const _).add hminus) hplus,
    integral_add (f := fun _x : ℝ => |Real.log s|)
      (g := fun x : ℝ => |Real.log (x - standardBoundaryRootMinus m s)|)
      (integrable_const _) hminus] at hbound
  have hconst : (∫ _x in Icc (0 : ℝ) 1, |Real.log s|) = |Real.log s| := by simp
  rw [hconst] at hbound
  obtain ⟨hrminus, hrplus⟩ := standard_boundary_roots_mem hm hs
  linarith [translated_log_abs_integral_le hrminus, translated_log_abs_integral_le hrplus]

theorem standard_bubble_upper_log_norm_bound (m s x : ℝ) :
    ‖standardBubbleUpperLog m s x‖ ≤
      |Real.log (m ^ 2)| + |Real.log (standardBubbleRealDenominator m s x)| + Real.pi := by
  unfold standardBubbleUpperLog
  have hphase : ‖(if standardBubbleRealDenominator m s x < 0 then
      (Real.pi : ℂ) * Complex.I else 0)‖ ≤ Real.pi := by
    split_ifs
    · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    · simpa only [norm_zero] using Real.pi_pos.le
  calc
    _ ≤ ‖((Real.log (m ^ 2) - Real.log (standardBubbleRealDenominator m s x) : ℝ) : ℂ)‖ +
        ‖(if standardBubbleRealDenominator m s x < 0 then (Real.pi : ℂ) * Complex.I else 0)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (abs_sub _ _) hphase

theorem standard_bubble_upper_boundary_norm_log_bound {m s : ℝ}
    (hm : 0 < m) (hs : 4 * m ^ 2 < s) :
    ‖standardBubbleUpperBoundary m s‖ ≤
      (|Real.log (m ^ 2)| + |Real.log s| + 6 + Real.pi) / (16 * Real.pi ^ 2) := by
  have hI := standard_bubble_upper_log_integrable m s
  have hL := standard_bubble_denominator_log_integrable m s
  have hmajor : IntegrableOn (fun x : ℝ =>
      |Real.log (m ^ 2)| + |Real.log (standardBubbleRealDenominator m s x)| + Real.pi) (Icc (0 : ℝ) 1) :=
    ((integrable_const _).add hL).add (integrable_const _)
  have hbound := integral_mono_ae hI.norm hmajor
    (Eventually.of_forall (standard_bubble_upper_log_norm_bound m s))
  rw [integral_add (f := fun x : ℝ => |Real.log (m ^ 2)| + |Real.log (standardBubbleRealDenominator m s x)|)
      (g := fun _x : ℝ => Real.pi) ((integrable_const _).add hL) (integrable_const _),
    integral_add (f := fun _x : ℝ => |Real.log (m ^ 2)|)
      (g := fun x : ℝ => |Real.log (standardBubbleRealDenominator m s x)|)
      (integrable_const _) hL] at hbound
  have hconst (c : ℝ) : (∫ _x in Icc (0 : ℝ) 1, c) = c := by simp
  rw [hconst, hconst] at hbound
  unfold standardBubbleUpperBoundary
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 16 * Real.pi ^ 2)]
  calc
    _ ≤ (16 * Real.pi ^ 2)⁻¹ * ∫ x in Icc (0 : ℝ) 1, ‖standardBubbleUpperLog m s x‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ (16 * Real.pi ^ 2)⁻¹ * (|Real.log (m ^ 2)| + |Real.log s| + 6 + Real.pi) :=
      mul_le_mul_of_nonneg_left (hbound.trans (by
        have hh := standard_boundary_denominator_abs_log_bound hm hs
        linarith)) (by positivity)
    _ = _ := by ring

theorem standard_bubble_upper_boundary_norm_linear_bound {m s : ℝ}
    (hm : 0 < m) (hs : 4 * m ^ 2 < s) (hsone : 1 ≤ s) :
    ‖standardBubbleUpperBoundary m s‖ ≤
      ((|Real.log (m ^ 2)| + 7 + Real.pi) / (16 * Real.pi ^ 2)) * s := by
  have hspos : 0 < s := zero_lt_one.trans_le hsone
  have hlog : |Real.log s| ≤ s := by
    rw [abs_of_nonneg (Real.log_nonneg hsone)]
    exact Real.log_le_self hspos.le
  have hbudget : |Real.log (m ^ 2)| + |Real.log s| + 6 + Real.pi ≤
      (|Real.log (m ^ 2)| + 7 + Real.pi) * s := by
    have hh := mul_le_mul_of_nonneg_left hsone
      (by positivity : 0 ≤ |Real.log (m ^ 2)| + 6 + Real.pi)
    nlinarith
  exact (standard_bubble_upper_boundary_norm_log_bound hm hs).trans
    ((div_le_div_of_nonneg_right hbudget (by positivity)).trans_eq (by ring))

theorem standard_bubble_upper_boundary_eventual_linear_bound {m : ℝ} (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ s : ℝ in atTop, ‖standardBubbleUpperBoundary m s‖ ≤ C * s := by
  refine ⟨(|Real.log (m ^ 2)| + 7 + Real.pi) / (16 * Real.pi ^ 2), by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (4 * m ^ 2), eventually_ge_atTop (1 : ℝ)] with s hs hsone
  exact standard_bubble_upper_boundary_norm_linear_bound hm hs hsone

end UV
