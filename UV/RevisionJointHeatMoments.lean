import UV.RevisionJointHeat
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Inverse moments for the actual correlated law obtained by sampling a
single depth and then independent conditional heat variables. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators

namespace UV.RevisionJointHeat

/-- The edge variables are independent before multiplication by the random
shared depth. The pushforward is the correlated law of their heat lapses. -/
def sharedDepthHeatLaw {ι : Type*} [Fintype ι] (w : Measure ℝ) : Measure (ι → ℝ) :=
  (w.prod (Measure.pi fun _ : ι => oqedMeasure 0)).map
    (fun z => fun j => (2 * z.1) ^ 2 * z.2 j)

instance {ι : Type*} [Fintype ι] (w : Measure ℝ) [IsProbabilityMeasure w] :
    IsProbabilityMeasure (sharedDepthHeatLaw (ι := ι) w) := by
  letI := oqedMeasure_zero_probability
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  apply measurable_pi_lambda
  intro j
  have h : Measurable (fun z : ℝ × (ι → ℝ) => z.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  fun_prop

/-- The same law expressed as the depth-averaged conditional product. The
statement is for arbitrary measurable tests in the extended nonnegative reals,
including indicator functions and tests with divergent integrals. -/
theorem sharedDepthHeatLaw_lintegral {ι : Type*} [Fintype ι]
    (w : Measure ℝ) [IsFiniteMeasure w] (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ell, f ell ∂sharedDepthHeatLaw w) =
      ∫⁻ r, (∫⁻ ell, f ell ∂Measure.pi fun _ : ι => oqedHeatMeasure (2 * r) 0) ∂w := by
  classical
  have h : Measurable (fun z : ℝ × (ι → ℝ) => fun j => (2 * z.1) ^ 2 * z.2 j) := by
    apply measurable_pi_lambda
    intro j
    have hj : Measurable (fun z : ℝ × (ι → ℝ) => z.2 j) :=
      (measurable_pi_apply j).comp measurable_snd
    fun_prop
  rw [sharedDepthHeatLaw, lintegral_map hf h,
    lintegral_prod (fun z : ℝ × (ι → ℝ) => f (fun j => (2 * z.1) ^ 2 * z.2 j))
      (hf.comp h).aemeasurable]
  apply lintegral_congr
  intro r
  have hm (j : ι) : Measurable (fun t : ℝ => (2 * r) ^ 2 * t) := by fun_prop
  have hmap : (Measure.pi fun _ : ι => oqedHeatMeasure (2 * r) 0) =
      (Measure.pi fun _ : ι => oqedMeasure 0).map (fun t j => (2*r)^2 * t j) := by
    rw [Measure.pi_map_pi (f := fun _ t => (2 * r) ^ 2 * t)
      (fun j => (hm j).aemeasurable)]
    simp only [oqedHeatMeasure, mul_zero]
  rw [hmap, lintegral_map hf (by
      apply measurable_pi_lambda
      intro j
      exact (hm j).comp (measurable_pi_apply j))]

/-- Exact one-line inverse moment at shared depth `r` and zero shift. -/
theorem sharedDepth_inverseMoment {r u : ℝ} (hr : 0 < r) (hu : -(1 / 2 : ℝ) < u) :
    inverseMoment (oqedHeatMeasure (2 * r) 0) u =
      ENNReal.ofReal (Gamma (u + 1 / 2) / sqrt π * r ^ (-2 * u)) := by
  rw [oqedHeatMeasure_inverseMoment (mul_pos two_pos hr), mul_zero,
    oqedInverseMoment_zero hu, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have htwo : (2 : ℝ) ^ (-2 * u) * (4 : ℝ) ^ u = 1 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
    simp
  rw [Real.mul_rpow two_pos.le hr.le]
  calc
    _ = ((2 : ℝ) ^ (-2 * u) * (4 : ℝ) ^ u) *
        (Gamma (u + 1 / 2) / sqrt π * r ^ (-2 * u)) := by ring
    _ = _ := by rw [htwo, one_mul]

private theorem conditional_prod_inverseMoment {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (hu : ∀ j, -(1 / 2 : ℝ) < u j) {r : ℝ} (hr : 0 < r) :
    (∫⁻ ell, ENNReal.ofReal (∏ j, (ell : ι → ℝ) j ^ (-u j))
      ∂Measure.pi (fun _ : ι => oqedHeatMeasure (2 * r) 0)) =
      ∏ j, inverseMoment (oqedHeatMeasure (2 * r) 0) (u j) := by
  classical
  let μ := oqedHeatMeasure (2 * r) 0
  have h2r : 0 < 2 * r := by positivity
  have hae : ∀ᵐ x ∂μ, 0 < x := by
    rw [ae_iff]
    convert oqedHeatMeasure_nonnegative_support h2r 0 using 2
    ext x
    simp
  have hres : μ.restrict (Ioi 0) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hm (j : ι) : Measurable (fun x : ℝ => x ^ (-u j)) := by fun_prop
  have hi (j : ι) : Integrable (fun x : ℝ => x ^ (-u j)) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable (hm j).aestronglyMeasurable
      (hae.mono fun x hx => Real.rpow_nonneg hx.le _)).mp
    have hh := oqedHeatMeasure_inverseMoment_finite (M := 0) h2r (hu j)
    rwa [inverseMoment, hres, lt_top_iff_ne_top] at hh
  have hnn (j : ι) : ∀ᵐ x ∂μ, 0 ≤ x ^ (-u j) :=
    hae.mono fun x hx => Real.rpow_nonneg hx.le _
  have hjoint : ∀ᵐ ell ∂Measure.pi (fun _ : ι => μ), ∀ j, 0 < (ell : ι → ℝ) j :=
    ae_all_iff.mpr fun j => (Measure.quasiMeasurePreserving_eval (fun _ : ι => μ) j).ae hae
  have hpi := Integrable.fintype_prod hi
  rw [← ofReal_integral_eq_lintegral_ofReal hpi
    (hjoint.mono fun _ h => Finset.prod_nonneg fun j _ => Real.rpow_nonneg (h j).le _),
    integral_fintype_prod_eq_prod (fun j (x : ℝ) => x ^ (-u j)),
    ENNReal.ofReal_prod_of_nonneg (fun j _ => integral_nonneg_of_ae (hnn j))]
  apply Finset.prod_congr rfl
  intro j _
  rw [inverseMoment, hres, ← ofReal_integral_eq_lintegral_ofReal (hi j) (hnn j)]

/-- Nonnegative extended joint moment identity. It remains exact even when
one shared-depth moment diverges. -/
theorem sharedDepth_joint_inverseMoment {ι : Type*} [Fintype ι]
    (w : Measure ℝ) [IsFiniteMeasure w] (hw : ∀ᵐ r ∂w, 0 < r)
    (u : ι → ℝ) (hu : ∀ j, 0 < u j) :
    (∫⁻ ell, ENNReal.ofReal (∏ j, (ell : ι → ℝ) j ^ (-u j)) ∂sharedDepthHeatLaw w) =
      ENNReal.ofReal (∏ j, Gamma (u j + 1 / 2) / sqrt π) *
        ∫⁻ r, ENNReal.ofReal (r ^ (-2 * ∑ j, u j)) ∂w := by
  classical
  have hm : Measurable (fun ell : ι → ℝ =>
      ENNReal.ofReal (∏ j, ell j ^ (-u j))) := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro j _
    have h := measurable_pi_apply (X := fun _ : ι => ℝ) j
    fun_prop
  rw [sharedDepthHeatLaw_lintegral w _ hm]
  have hmr : Measurable (fun r : ℝ => ENNReal.ofReal (r ^ (-2 * ∑ j, u j))) := by fun_prop
  rw [← lintegral_const_mul _ hmr]
  apply lintegral_congr_ae
  filter_upwards [hw] with r hr
  have hu' : ∀ j, -(1 / 2 : ℝ) < u j := fun j => by linarith [hu j]
  rw [conditional_prod_inverseMoment u hu' hr]
  simp_rw [sharedDepth_inverseMoment hr (hu' _)]
  have hG (j : ι) : 0 ≤ Gamma (u j + 1 / 2) / sqrt π :=
    div_nonneg (Gamma_pos_of_pos (by linarith [hu j])).le (sqrt_nonneg _)
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => mul_nonneg (hG j) (Real.rpow_nonneg hr.le _)),
    Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hr, ← Finset.mul_sum,
    ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => hG j)]

/-- A common depth is positive almost surely precisely where the conditional
line laws are supported on positive lapses. -/
theorem sharedDepthHeatLaw_ae_pos {ι : Type*} [Fintype ι]
    (w : Measure ℝ) [IsFiniteMeasure w] (hw : ∀ᵐ r ∂w, 0 < r) :
    ∀ᵐ ell ∂sharedDepthHeatLaw w, ∀ j : ι, 0 < ell j := by
  rw [ae_all_iff]
  intro j
  let s : Set (ι → ℝ) := (Function.eval j) ⁻¹' Iic (0 : ℝ)
  have hs : MeasurableSet s := (measurable_pi_apply (X := fun _ : ι => ℝ) j) measurableSet_Iic
  rw [ae_iff, show {ell : ι → ℝ | ¬ 0 < ell j} = s by ext ell; simp [s],
    ← lintegral_indicator_one hs, sharedDepthHeatLaw_lintegral w (s.indicator (1 : (ι → ℝ) → ℝ≥0∞))
      (measurable_const.indicator hs)]
  have hzero : ∀ᵐ r ∂w, (∫⁻ ell, s.indicator (1 : (ι → ℝ) → ℝ≥0∞) ell
      ∂Measure.pi (fun _ : ι => oqedHeatMeasure (2 * r) 0)) = 0 := by
    filter_upwards [hw] with r hr
    rw [lintegral_indicator_one hs]
    exact Measure.pi_eval_preimage_null (fun _ : ι => oqedHeatMeasure (2 * r) 0)
      (oqedHeatMeasure_nonnegative_support (mul_pos two_pos hr) 0)
  rw [lintegral_congr_ae hzero, lintegral_zero]

private theorem inverseMoment_of_truncated {rref H : ℝ} (href : 0 < rref)
    (hH : 0 ≤ H) (w : Measure ℝ) [IsFiniteMeasure w]
    (hcut : IntegrableOn (fun r : ℝ => r ^ (-H)) (Ioc 0 rref) w) :
    inverseMoment w H < ⊤ := by
  have htail : IntegrableOn (fun r : ℝ => r ^ (-H)) (Ioi rref) w := by
    apply (integrable_const (rref ^ (-H))).mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (href.trans hr).le _)]
    exact Real.rpow_le_rpow_of_nonpos href hr.le (neg_nonpos.mpr hH)
  have hfull : IntegrableOn (fun r : ℝ => r ^ (-H)) (Ioi 0) w := by
    rw [← Ioc_union_Ioi_eq_Ioi href.le]
    exact hcut.union htail
  rw [inverseMoment, lt_top_iff_ne_top]
  exact (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    ((ae_restrict_mem measurableSet_Ioi).mono fun r hr => Real.rpow_nonneg hr.le _)).mpr hfull

/-- The worst selected-order truncated depth moment suffices for every term
in the exact joint Gaussian budget. The law has no mass at zero by `hw`. -/
theorem sharedDepth_jointBudget_integrable
    {ι A : Type*} [Fintype ι] [Fintype A] (w : Measure ℝ) [IsProbabilityMeasure w]
    (hw : ∀ᵐ r ∂w, 0 < r) (c : A → ℝ) (d : A → ι → ℝ) (hd : ∀ a j, 0 ≤ d a j)
    {D rref : ℝ} (hD : 0 ≤ D) (hsum : ∀ a, ∑ j, d a j ≤ D) (href : 0 < rref)
    (hcut : IntegrableOn (fun r : ℝ => r ^ (-(2 * Fintype.card ι + D))) (Ioc 0 rref) w) :
    Integrable (jointBudget (fun j ell => ell j) d (fun a _ => c a)) (sharedDepthHeatLaw w) := by
  classical
  let H : ℝ := 2 * Fintype.card ι + D
  have hwfull : inverseMoment w H < ⊤ := inverseMoment_of_truncated href (by dsimp [H]; positivity) w hcut
  have hrestrict : w.restrict (Ioi 0) = w := Measure.restrict_eq_self_of_ae_mem hw
  have hpositive := sharedDepthHeatLaw_ae_pos (ι := ι) w hw
  let degree (a : A) (j : ι) (b : Fin 2) := if b = 0 then 0 else d a j
  have hterm (a : A) (B : ι → Fin 2) :
      Integrable (fun ell : ι → ℝ => ∏ j, gaussianBudget (degree a j (B j)) (ell j))
        (sharedDepthHeatLaw w) := by
    let u (j : ι) := 1 + degree a j (B j) / 2
    have hdeg (j : ι) : 0 ≤ degree a j (B j) ∧ degree a j (B j) ≤ d a j := by
      unfold degree
      split_ifs <;> exact ⟨by first | rfl | exact hd a j, by first | rfl | exact hd a j⟩
    have hu (j : ι) : 0 < u j := by dsimp [u]; linarith [(hdeg j).1]
    have hU : 2 * ∑ j, u j ≤ H := by
      dsimp [u, H]
      rw [Finset.mul_sum]
      simp_rw [show ∀ x : ℝ, 2 * (1 + x / 2) = 2 + x by intro x; ring]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      linarith [(Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (hdeg j).2)).trans (hsum a)]
    have hwU := inverseMoment_lower_order_finite w
      (mul_nonneg two_pos.le (Finset.sum_nonneg fun j _ => (hu j).le)) hU hwfull
    rw [inverseMoment, hrestrict] at hwU
    have hj := sharedDepth_joint_inverseMoment w hw u hu
    change Integrable (fun ell : ι → ℝ => ∏ j, π ^ 2 * Gamma (u j) * ell j ^ (-u j))
      (sharedDepthHeatLaw w)
    rw [← lintegral_ofReal_ne_top_iff_integrable (by
      apply Measurable.aestronglyMeasurable
      apply Finset.measurable_prod
      intro j _
      have hm := measurable_pi_apply (X := fun _ : ι => ℝ) j
      fun_prop) (hpositive.mono fun ell h =>
      Finset.prod_nonneg fun j _ => mul_nonneg
        (mul_nonneg (sq_nonneg π) (Gamma_pos_of_pos (hu j)).le) (Real.rpow_nonneg (h j).le _))]
    simp_rw [Finset.prod_mul_distrib (s := Finset.univ) (f := fun j => π ^ 2 * Gamma (u j))]
    have hG : 0 ≤ ∏ j, π ^ 2 * Gamma (u j) :=
      Finset.prod_nonneg fun j _ => mul_nonneg (sq_nonneg _) (Gamma_pos_of_pos (hu j)).le
    simp_rw [ENNReal.ofReal_mul hG]
    rw [lintegral_const_mul]
    · rw [hj]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simpa only [neg_mul] using hwU.ne))
    · apply Measurable.ennreal_ofReal
      apply Finset.measurable_prod
      intro j _
      have hm := measurable_pi_apply (X := fun _ : ι => ℝ) j
      fun_prop
  unfold jointBudget
  apply integrable_finset_sum
  intro a _
  apply Integrable.const_mul
  have he (ell : ι → ℝ) : (∏ j, (gaussianBudget 0 (ell j) + gaussianBudget (d a j) (ell j))) =
      ∑ B : ι → Fin 2, ∏ j, gaussianBudget (degree a j (B j)) (ell j) := by
    simpa [Fin.sum_univ_two, degree] using
      Fintype.prod_sum (fun j (i : Fin 2) => gaussianBudget (degree a j i) (ell j))
  simp_rw [he]
  exact integrable_finset_sum _ (fun B _ => hterm a B)

end UV.RevisionJointHeat
