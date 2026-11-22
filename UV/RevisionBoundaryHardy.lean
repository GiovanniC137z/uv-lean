import UV.RevisionBoundaryHeat
import Mathlib.MeasureTheory.Function.L2Space

/-! The marked-return Hardy estimate on one-dimensional normal states in their
continuous primitive representation. Weighted Cauchy–Schwarz followed by
Tonelli gives the sharp constant four, including square-integrable derivatives
without pointwise differentiability of the state. -/

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal Topology

namespace UV.RevisionBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem quarter_sq (t : ℝ) (ht : 0 ≤ t) (r : ℝ) :
    (t ^ r) ^ 2 = t ^ (2 * r) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num [mul_comm]

private theorem weighted_primitive_bound {x : ℝ} (hx : 0 < x) {g : ℝ → E}
    (hg : MemLp g 2 volume) :
    ‖∫ t in Ioo 0 x, g t‖ ^ 2 ≤
      2 * x ^ (1 / 2 : ℝ) * ∫ t in Ioo 0 x, t ^ (1 / 2 : ℝ) * ‖g t‖ ^ 2 := by
  let μ := volume.restrict (Ioo 0 x)
  let a : ℝ → ℝ := fun t => t ^ (-1 / 4 : ℝ)
  let b : ℝ → ℝ := fun t => t ^ (1 / 4 : ℝ) * ‖g t‖
  have ae : ∀ᵐ t ∂μ, t ∈ Ioo 0 x := ae_restrict_mem measurableSet_Ioo
  have ha : MemLp a 2 μ := by
    apply (memLp_two_iff_integrable_sq (measurable_id.pow_const _).aestronglyMeasurable).mpr
    apply ((intervalIntegral.integrableOn_Ioo_rpow_iff hx).mpr (show (-1 : ℝ) < -1 / 2 by
      norm_num)).congr
    filter_upwards [ae] with t ht
    change t ^ (-1 / 2 : ℝ) = (t ^ (-1 / 4 : ℝ)) ^ 2
    rw [quarter_sq t ht.1.le]
    norm_num
  have hgs := ((memLp_two_iff_integrable_sq_norm hg.1).mp hg).restrict (s := Ioo 0 x)
  have hbs : Integrable (fun t => b t ^ 2) μ := by
    apply (hgs.const_mul (x ^ (1 / 2 : ℝ))).mono'
    · exact ((measurable_id.pow_const _).aestronglyMeasurable.mul
        (hg.mono_measure Measure.restrict_le_self).1.norm).pow 2
    · filter_upwards [ae] with t ht
      change ‖(t ^ (1 / 4 : ℝ) * ‖g t‖) ^ 2‖ ≤ x ^ (1 / 2 : ℝ) * ‖g t‖ ^ 2
      rw [Real.norm_of_nonneg (sq_nonneg _), mul_pow, quarter_sq t ht.1.le]
      norm_num
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht.1.le ht.2.le (by norm_num)) (sq_nonneg _)
  have hb : MemLp b 2 μ :=
    (memLp_two_iff_integrable_sq ((measurable_id.pow_const _).aestronglyMeasurable.mul
      (hg.mono_measure Measure.restrict_le_self).1.norm)).mpr hbs
  have hab : (fun t => a t * b t) =ᵐ[μ] (fun t => ‖g t‖) := by
    filter_upwards [ae] with t ht
    change t ^ (-1 / 4 : ℝ) * (t ^ (1 / 4 : ℝ) * ‖g t‖) = ‖g t‖
    rw [← mul_assoc, ← Real.rpow_add ht.1]
    norm_num
  have ha0 : 0 ≤ᵐ[μ] a := ae.mono fun t ht => Real.rpow_nonneg ht.1.le _
  have hb0 : 0 ≤ᵐ[μ] b :=
    ae.mono fun t ht => mul_nonneg (Real.rpow_nonneg ht.1.le _) (norm_nonneg _)
  have hhold := integral_mul_le_Lp_mul_Lq_of_nonneg
    (by norm_num [Real.holderConjugate_iff] : Real.HolderConjugate 2 2)
    ha0 hb0
    (by convert ha using 1; norm_num)
    (by convert hb using 1; norm_num)
  rw [integral_congr_ae hab] at hhold
  norm_num at hhold
  have hia : (∫ t, a t ^ 2 ∂μ) = 2 * x ^ (1 / 2 : ℝ) := by
    calc
      _ = ∫ t in Ioo 0 x, t ^ (-1 / 2 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae] with t ht
        change (t ^ (-1 / 4 : ℝ)) ^ 2 = _
        rw [quarter_sq _ ht.1.le]
        norm_num
      _ = _ := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.le]
        rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
        norm_num [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
        ring
  have hib : (∫ t, b t ^ 2 ∂μ) = ∫ t in Ioo 0 x, t ^ (1 / 2 : ℝ) * ‖g t‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae] with t ht
    change (t ^ (1 / 4 : ℝ) * ‖g t‖) ^ 2 = _
    rw [mul_pow, quarter_sq _ ht.1.le]
    norm_num
  have hba : 0 ≤ ∫ t, b t ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have haa : 0 ≤ ∫ t, a t ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hh : ‖∫ t in Ioo 0 x, g t‖ ≤ (∫ t, a t ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
      (∫ t, b t ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    exact (norm_integral_le_integral_norm _).trans hhold
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
  rw [mul_pow, quarter_sq _ haa, quarter_sq _ hba] at hsq
  norm_num at hsq
  rwa [hia, hib] at hsq

omit [NormedSpace ℝ E] in
private theorem half_line_schur {g : ℝ → E} (hg : StronglyMeasurable g) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (x ^ (-3 / 2 : ℝ)) *
       ∫⁻ t in Ioo 0 x, ENNReal.ofReal (t ^ (1 / 2 : ℝ) * ‖g t‖ ^ 2)) =
      2 * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (‖g t‖ ^ 2) := by
  let a : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (x ^ (-3 / 2 : ℝ))
  let b : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (1 / 2 : ℝ) * ‖g t‖ ^ 2)
  let k : ℝ → ℝ → ℝ≥0∞ := fun x t => if 0 < t ∧ t < x then a x * b t else 0
  have hma : Measurable a := by unfold a; fun_prop
  have hmb : Measurable b :=
    ((measurable_id.pow_const _).mul (hg.norm.measurable.pow_const _)).ennreal_ofReal
  have hmk : Measurable (Function.uncurry k) := by
    exact Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)) ((hma.comp measurable_fst).mul
      (hmb.comp measurable_snd)) measurable_const
  calc
    _ = ∫⁻ x in Ioi (0 : ℝ), ∫⁻ t, k x t := by
      refine lintegral_congr fun x => ?_
      rw [← lintegral_const_mul _ hmb, ← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro t
      change (Ioo 0 x).indicator (fun t => a x * b t) t = k x t
      simp [k, Set.indicator, mem_Ioo]
    _ = ∫⁻ t, ∫⁻ x in Ioi (0 : ℝ), k x t := lintegral_lintegral_swap hmk.aemeasurable
    _ = _ := by
      rw [← lintegral_const_mul _ ((hg.norm.measurable.pow_const (2 : ℕ)).ennreal_ofReal),
        ← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro t
      by_cases ht : 0 < t
      · have ha : IntegrableOn (fun x : ℝ => x ^ (-3 / 2 : ℝ)) (Ioi t) :=
          integrableOn_Ioi_rpow_of_lt (by norm_num) ht
        have hk : (fun x => k x t) = (Ioi t).indicator (fun x => a x * b t) := by
          funext x
          simp [k, ht, Set.indicator]
        rw [hk, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
          inter_eq_left.mpr (Ioi_subset_Ioi ht.le), lintegral_mul_const _ hma]
        rw [show (∫⁻ x in Ioi t, a x) = ENNReal.ofReal (2 * t ^ (-1 / 2 : ℝ)) by
          unfold a
          rw [← ofReal_integral_eq_lintegral_ofReal ha
            ((ae_restrict_mem measurableSet_Ioi).mono fun x hx =>
              Real.rpow_nonneg (ht.trans hx).le _)]
          rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) ht]
          norm_num
          rw [show t ^ (-(1 / 2) : ℝ) / (1 / 2 : ℝ) =
            2 * t ^ (-(1 / 2) : ℝ) by ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]]
        rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
        unfold b
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * t ^ (-1 / 2 : ℝ)),
          ← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        rw [← mul_assoc, mul_assoc (2 : ℝ), ← Real.rpow_add ht]
        norm_num
      · simp [k, ht, Set.indicator]

theorem half_line_hardy {φ g : ℝ → E} (hgm : StronglyMeasurable g)
    (hg : MemLp g 2 volume) (hφ : ∀ x > 0, φ x = ∫ t in Ioo 0 x, g t) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (‖φ x‖ ^ 2 / x ^ 2)) ≤
      4 * ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (‖g x‖ ^ 2) := by
  let h : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (x ^ (-3 / 2 : ℝ)) *
      ∫⁻ t in Ioo 0 x, ENNReal.ofReal (t ^ (1 / 2 : ℝ) * ‖g t‖ ^ 2)
  have hmeas : Measurable h := by
    unfold h
    refine (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (x ^ (-3 / 2 : ℝ))).mul ?_
    simp_rw [← lintegral_indicator measurableSet_Ioo]
    let b : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (1 / 2 : ℝ) * ‖g t‖ ^ 2)
    have hm : Measurable (fun p : ℝ × ℝ => if 0 < p.2 ∧ p.2 < p.1 then b p.2 else 0) :=
      Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_fst))
        (((measurable_id.pow_const _).mul (hgm.norm.measurable.pow_const _)).ennreal_ofReal.comp
          measurable_snd) measurable_const
    simpa only [b, Set.indicator, mem_Ioo] using hm.lintegral_prod_right'
  calc
    _ ≤ ∫⁻ x in Ioi (0 : ℝ), 2 * h x := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : 0 < x := hx
      have hi : IntegrableOn (fun t : ℝ => t ^ (1 / 2 : ℝ) * ‖g t‖ ^ 2) (Ioo 0 x) := by
        apply (((memLp_two_iff_integrable_sq_norm hg.1).mp hg).restrict (s := Ioo 0 x)
            |>.const_mul (x ^ (1 / 2 : ℝ))).mono'
        · exact (((measurable_id.pow_const _).mul (hgm.norm.measurable.pow_const _)).aestronglyMeasurable)
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (sq_nonneg _))]
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht.1.le ht.2.le (by norm_num)) (sq_nonneg _)
      unfold h
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        ((ae_restrict_mem measurableSet_Ioo).mono fun t ht =>
          mul_nonneg (Real.rpow_nonneg ht.1.le _) (sq_nonneg _)),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ x ^ (-3 / 2 : ℝ))]
      rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      apply ENNReal.ofReal_le_ofReal
      rw [hφ x hx', div_le_iff₀ (sq_pos_of_pos hx')]
      have hh := weighted_primitive_bound hx' hg
      have hpow : x ^ (-3 / 2 : ℝ) * x ^ 2 = x ^ (1 / 2 : ℝ) := by
        rw [show x ^ (2 : ℕ) = x ^ (2 : ℝ) by norm_num [Real.rpow_natCast],
          ← Real.rpow_add hx']
        norm_num
      convert hh using 1
      rw [show 2 * (x ^ (-3 / 2 : ℝ) * (∫ t in Ioo 0 x, t ^ (1 / 2 : ℝ) * ‖g t‖ ^ 2)) *
          x ^ 2 = 2 * (x ^ (-3 / 2 : ℝ) * x ^ 2) *
            (∫ t in Ioo 0 x, t ^ (1 / 2 : ℝ) * ‖g t‖ ^ 2) by ring, hpow]
    _ = 2 * ∫⁻ x in Ioi (0 : ℝ), h x := lintegral_const_mul _ hmeas
    _ = _ := by rw [show ∫⁻ x in Ioi (0 : ℝ), h x = _ from half_line_schur hgm]; ring


private theorem lintegral_halves (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x = (∫⁻ x in Iio (0 : ℝ), f x) + ∫⁻ x in Ioi (0 : ℝ), f x := by
  rw [restrict_Iio_eq_restrict_Iic, ← lintegral_union measurableSet_Ioi (Iic_disjoint_Ioi le_rfl),
    Iic_union_Ioi, Measure.restrict_univ]

private theorem lintegral_neg_Ioi {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in Ioi (0 : ℝ), f (-x) = ∫⁻ x in Iio (0 : ℝ), f x := by
  have hs : (fun x : ℝ => -x) ⁻¹' Iio (0 : ℝ) = Ioi 0 := by
    ext x
    simp
  have hh := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
    (s := Iio (0 : ℝ)) measurableSet_Iio hf
  change (∫⁻ x in ((fun t : ℝ => -t) ⁻¹' Iio (0 : ℝ)), f (-x)) =
    ∫⁻ x in Iio (0 : ℝ), f x at hh
  rwa [hs] at hh

/-- The global Hardy inequality in the integral-representative formulation of
one-dimensional `H¹`. Here `g` is the square-integrable normal derivative,
and the continuous representative has value zero at the marked point. -/
theorem normal_hardy {φ g : ℝ → E} (hφc : Continuous φ) (hg : MemLp g 2 volume)
    (hφ : ∀ x, φ x = ∫ t in (0 : ℝ)..x, g t) :
    (∫⁻ x, ENNReal.ofReal (‖φ x‖ ^ 2 / x ^ 2)) ≤
      4 * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) := by
  let G := hg.1.mk g
  have hGm : StronglyMeasurable G := hg.1.stronglyMeasurable_mk
  have hge : g =ᵐ[volume] G := hg.1.ae_eq_mk
  have hG : MemLp G 2 volume := hg.ae_eq hge
  have hφG : ∀ x, φ x = ∫ t in (0 : ℝ)..x, G t := by
    intro x
    rw [hφ x]
    exact intervalIntegral.integral_congr_ae (hge.mono fun _ h _ => h)
  have hpos : ∀ x > 0, φ x = ∫ t in Ioo 0 x, G t := by
    intro x hx
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.le, hφG]
  have hneg : ∀ x > 0, φ (-x) = ∫ t in Ioo 0 x, -G (-t) := by
    intro x hx
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx.le,
      intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg, neg_zero,
      ← intervalIntegral.integral_symm, hφG]
  have hgn : MemLp (fun t => -G (-t)) 2 volume :=
    (hG.comp_measurePreserving (Measure.measurePreserving_neg volume)).neg
  have hgnm : StronglyMeasurable (fun t : ℝ => -G (-t)) :=
    (hGm.comp_measurable measurable_neg).neg
  have hn := half_line_hardy hgnm hgn hneg
  have hp := half_line_hardy hGm hG hpos
  have he : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2)) =
      ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) := by
    apply lintegral_congr_ae
    filter_upwards [hge] with x hx
    rw [hx]
  simp only [norm_neg] at hn
  have hnk (x : ℝ) : ENNReal.ofReal (‖φ (-x)‖ ^ 2 / x ^ 2) =
      ENNReal.ofReal (‖φ (-x)‖ ^ 2 / (-x) ^ 2) := by rw [neg_sq]
  simp_rw [hnk] at hn
  have hmφ : Measurable (fun x : ℝ => ENNReal.ofReal (‖φ x‖ ^ 2 / x ^ 2)) :=
    ((hφc.norm.pow 2).measurable.div (continuous_id.pow 2).measurable).ennreal_ofReal
  rw [lintegral_neg_Ioi hmφ,
    lintegral_neg_Ioi (hGm.norm.measurable.pow_const (2 : ℕ)).ennreal_ofReal] at hn
  rw [he, lintegral_halves (fun x => ENNReal.ofReal (‖φ x‖ ^ 2 / x ^ 2)),
    lintegral_halves (fun x => ENNReal.ofReal (‖G x‖ ^ 2)), mul_add]
  exact add_le_add hn hp


end UV.RevisionBoundary
