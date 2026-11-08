import UV.WardCommonCutoff
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The exact two-line QED convolution moment, including infinite values at
zero proper time. All exchanges below are nonnegative Tonelli exchanges. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal MeasureTheory

namespace UV

def qedSquareIntegral (ρ : Measure ℝ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ioi 0, ENNReal.ofReal (wardLaplaceKernel ρ a u ^ 2)

theorem qed_exponential_lintegral {b : ℝ} (hb : 0 ≤ b) :
    (∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-b * u))) =
      (ENNReal.ofReal b)⁻¹ := by
  rcases eq_or_lt_of_le hb with hzero | hpos
  · simp [← hzero]
  · have hi : IntegrableOn (fun u : ℝ => Real.exp (-b * u)) (Ioi 0) :=
      integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hpos) 0
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)),
      integral_exp_mul_Ioi (neg_lt_zero.mpr hpos) 0]
    simp [ENNReal.ofReal_inv_of_pos hpos]

theorem wardLaplaceKernel_square_lintegral (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (a : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ENNReal.ofReal (wardLaplaceKernel ρ a u ^ 2) =
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal
        (Real.exp (-(p.1 + p.2) * (a ^ 2 * u))) ∂ρ.prod ρ := by
  rw [wardLaplaceKernel_eq ρ a hu]
  have hi := nonnegative_laplace_integrable ρ hp (mul_nonneg (sq_nonneg a) hu)
  have he : ENNReal.ofReal (laplace ρ (a ^ 2 * u)) =
      ∫⁻ τ, ENNReal.ofReal (Real.exp (-τ * (a ^ 2 * u))) ∂ρ :=
    ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _))
  have hn : 0 ≤ laplace ρ (a ^ 2 * u) := integral_nonneg (fun _ => Real.exp_nonneg _)
  rw [ENNReal.ofReal_pow hn 2, pow_two, he,
    ← lintegral_prod_mul (by fun_prop) (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards with p
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

theorem qed_laplace_pair_integral {a τ σ : ℝ} (ha : a ≠ 0)
    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) :
    (∫⁻ u : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-(τ + σ) * (a ^ 2 * u)))) =
      ENNReal.ofReal ((a ^ 2)⁻¹) * (ENNReal.ofReal (τ + σ))⁻¹ := by
  have he (u : ℝ) : -(τ + σ) * (a ^ 2 * u) = -(a ^ 2 * (τ + σ)) * u := by ring
  simp_rw [he]
  rw [qed_exponential_lintegral (mul_nonneg (sq_nonneg a) (add_nonneg hτ hσ)),
    ENNReal.ofReal_mul (sq_nonneg a),
    ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top),
    ENNReal.ofReal_inv_of_pos (sq_pos_of_ne_zero ha)]

/-- The manuscript's equation `eq:QED-convolution-moment`, as an equality
in `[0,∞]`. Its proper-time integrand is literally infinite at `(0,0)`. -/
theorem qed_convolution_moment (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {a : ℝ} (ha : a ≠ 0) :
    qedSquareIntegral ρ a = ENNReal.ofReal ((a ^ 2)⁻¹) *
      ∫⁻ τ, ∫⁻ σ, (ENNReal.ofReal (τ + σ))⁻¹ ∂ρ ∂ρ := by
  unfold qedSquareIntegral
  have hp2 : ∀ᵐ p : ℝ × ℝ ∂ρ.prod ρ, 0 ≤ p.1 ∧ 0 ≤ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd))).mpr
    filter_upwards [hp] with τ hτ
    filter_upwards [hp] with σ hσ
    exact ⟨hτ, hσ⟩
  calc
    _ = ∫⁻ u in Ioi 0, ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal (Real.exp (-(p.1 + p.2) * (a ^ 2 * u))) ∂ρ.prod ρ := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact wardLaplaceKernel_square_lintegral ρ hp a hu.le
    _ = ∫⁻ p : ℝ × ℝ, (∫⁻ u : ℝ in Ioi 0,
        ENNReal.ofReal (Real.exp (-(p.1 + p.2) * (a ^ 2 * u))) ∂volume) ∂ρ.prod ρ :=
      lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ p : ℝ × ℝ,
        ENNReal.ofReal ((a ^ 2)⁻¹) * (ENNReal.ofReal (p.1 + p.2))⁻¹ ∂ρ.prod ρ := by
      apply lintegral_congr_ae
      filter_upwards [hp2] with p hp'
      exact qed_laplace_pair_integral ha hp'.1 hp'.2
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_prod _ (by fun_prop)]

theorem qed_convolution_moment_conv (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {a : ℝ} (ha : a ≠ 0) :
    qedSquareIntegral ρ a = ENNReal.ofReal ((a ^ 2)⁻¹) *
      ∫⁻ s, (ENNReal.ofReal s)⁻¹ ∂(ρ ∗ ρ) := by
  rw [Measure.lintegral_conv (by fun_prop)]
  exact qed_convolution_moment ρ hp ha

theorem nonnegative_inverse_lintegral (ν : Measure ℝ)
    (hp : ∀ᵐ s ∂ν, 0 ≤ s) :
    (∫⁻ s, (ENNReal.ofReal s)⁻¹ ∂ν) = extendedInverseMoment ν 1 := by
  have hs : ∀ᵐ s ∂ν, s ∈ Ici (0 : ℝ) := hp
  rw [extendedInverseMoment, Measure.restrict_eq_self_of_ae_mem hs]
  apply lintegral_congr_ae
  filter_upwards [hp] with s hs
  by_cases hz : s = 0
  · simp [hz]
  · rw [if_neg hz]
    rw [Real.rpow_neg_one, ENNReal.ofReal_inv_of_pos (lt_of_le_of_ne hs (Ne.symm hz))]

theorem qed_convolution_nonnegative_support (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) : ∀ᵐ τ ∂(ρ ∗ ρ), 0 ≤ τ := by
  rw [Measure.conv, ae_map_iff (by fun_prop :
    AEMeasurable (fun x : ℝ × ℝ => x.1 + x.2) (ρ.prod ρ)) measurableSet_Ici]
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le measurable_const (measurable_fst.add measurable_snd))).mpr
  filter_upwards [hp] with x hx
  filter_upwards [hp] with y hy
  exact add_nonneg hx hy

theorem qed_convolution_zero_atom (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) : (ρ ∗ ρ) {0} = ρ {0} * ρ {0} := by
  rw [Measure.conv, Measure.map_apply
    (by fun_prop : Measurable (fun x : ℝ × ℝ => x.1 + x.2)) (measurableSet_singleton 0)]
  rw [← Measure.prod_prod]
  apply measure_congr
  have hn : ∀ᵐ z ∂ρ.prod ρ, 0 ≤ z.1 ∧ 0 ≤ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd))).mpr
    filter_upwards [hp] with x hx
    filter_upwards [hp] with y hy
    exact ⟨hx, hy⟩
  filter_upwards [hn] with z hz
  apply propext
  change (z.1 + z.2 = 0) ↔ (z.1 = 0 ∧ z.2 = 0)
  constructor
  · intro he
    exact ⟨by linarith [hz.1, hz.2], by linarith [hz.1, hz.2]⟩
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

theorem qed_convolution_moment_extended (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {a : ℝ} (ha : a ≠ 0) :
    qedSquareIntegral ρ a = ENNReal.ofReal ((a ^ 2)⁻¹) * extendedInverseMoment (ρ ∗ ρ) 1 := by
  rw [qed_convolution_moment_conv ρ hp ha,
    nonnegative_inverse_lintegral (ρ ∗ ρ) (qed_convolution_nonnegative_support ρ hp)]

theorem qed_convolution_moment_finite_iff (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {a : ℝ} (ha : a ≠ 0) :
    qedSquareIntegral ρ a < ⊤ ↔ extendedInverseMoment (ρ ∗ ρ) 1 < ⊤ := by
  rw [qed_convolution_moment_extended ρ hp ha]
  have hc : ENNReal.ofReal ((a ^ 2)⁻¹) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr (sq_pos_of_ne_zero ha)))
  constructor
  · intro h
    rcases ENNReal.mul_lt_top_iff.mp h with hh | hz | hz
    · exact hh.2
    · exact (hc hz).elim
    · simp [hz]
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top

theorem qed_convolution_moment_finite_iff_no_atom (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {a : ℝ} (ha : a ≠ 0) :
    qedSquareIntegral ρ a < ⊤ ↔ ρ {0} = 0 ∧ inverseMoment (ρ ∗ ρ) 1 < ⊤ := by
  rw [qed_convolution_moment_finite_iff ρ hp ha, extendedInverseMoment_lt_top_iff,
    qed_convolution_zero_atom ρ hp]
  simp only [mul_eq_zero, or_self]

theorem qed_convolution_moment_of_finite (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {a : ℝ} (ha : a ≠ 0)
    (hQ : qedSquareIntegral ρ a < ⊤) :
    ρ {0} = 0 ∧ qedSquareIntegral ρ a =
      ENNReal.ofReal ((a ^ 2)⁻¹) * inverseMoment (ρ ∗ ρ) 1 := by
  have hz := ((qed_convolution_moment_finite_iff_no_atom ρ hp ha).mp hQ).1
  refine ⟨hz, ?_⟩
  rw [qed_convolution_moment_extended ρ hp ha, extendedInverseMoment_split,
    qed_convolution_zero_atom ρ hp, hz, mul_zero, mul_zero, zero_add]

theorem qed_square_integral_finite_iff (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (a : ℝ) :
    qedSquareIntegral ρ a < ⊤ ↔
      IntegrableOn (fun u => wardLaplaceKernel ρ a u ^ 2) (Ioi 0) := by
  unfold qedSquareIntegral
  rw [lt_top_iff_ne_top]
  exact lintegral_ofReal_ne_top_iff_integrable
    (((wardLaplaceKernel_continuous ρ hp a).pow 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))

/-- The exact measure test for the condition used in the general QED
obstruction: the convolution inverse first moment suffices, and a zero atom
is explicitly excluded. -/
theorem qed_square_integrable_iff_convolution_moment (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {a : ℝ} (ha : a ≠ 0) :
    IntegrableOn (fun u => wardLaplaceKernel ρ a u ^ 2) (Ioi 0) ↔
      ρ {0} = 0 ∧ inverseMoment (ρ ∗ ρ) 1 < ⊤ := by
  rw [← qed_square_integral_finite_iff ρ hp a]
  exact qed_convolution_moment_finite_iff_no_atom ρ hp ha

theorem qed_convolution_moment_real (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) {a : ℝ} (ha : a ≠ 0)
    (hQ : IntegrableOn (fun u => wardLaplaceKernel ρ a u ^ 2) (Ioi 0)) :
    (∫ u in Ioi 0, wardLaplaceKernel ρ a u ^ 2) =
      (a ^ 2)⁻¹ * (inverseMoment (ρ ∗ ρ) 1).toReal := by
  have hfin := (qed_square_integral_finite_iff ρ hp a).mpr hQ
  have he := (qed_convolution_moment_of_finite ρ hp ha hfin).2
  have ho : ENNReal.ofReal (∫ u in Ioi 0, wardLaplaceKernel ρ a u ^ 2) =
      qedSquareIntegral ρ a :=
    ofReal_integral_eq_lintegral_ofReal hQ
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  have hreal := congrArg ENNReal.toReal he
  rw [← ho, ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _)),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg a))] at hreal
  exact hreal

end UV
