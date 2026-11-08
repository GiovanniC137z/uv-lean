import UV.WardCommonCutoff
import UV.L2Correlation
import UV.RadialAveraging
import UV.QEDTail
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Asymptotics.Lemmas

/-! The exact one-loop integrability criterion and its bare-vertex
nontransversality consequence, including the massless free propagator. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped BigOperators Matrix Topology Matrix.Norms.Elementwise

namespace UV

theorem square_image_Ioi : (fun r : ℝ => r ^ 2) '' Ioi 0 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨r, hr, rfl⟩
    change 0 < r at hr
    exact sq_pos_of_pos hr
  · intro hu
    change 0 < u at hu
    exact ⟨Real.sqrt u, Real.sqrt_pos.mpr hu, Real.sq_sqrt hu.le⟩

theorem integrableOn_square_substitution (g : ℝ → ℝ) :
    IntegrableOn g (Ioi 0) ↔
      IntegrableOn (fun r : ℝ => 2 * r * g (r ^ 2)) (Ioi 0) := by
  have hh := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := fun r : ℝ => r ^ 2) (f' := fun r : ℝ => 2 * r)
    measurableSet_Ioi (fun r _ => (show HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r from
      by simpa using (hasDerivAt_id r).pow 2).hasDerivWithinAt)
    (show InjOn (fun r : ℝ => r ^ 2) (Ioi 0) from
      fun r hr s hs hrs => (sq_eq_sq₀ hr.le hs.le).mp hrs) g
  rw [square_image_Ioi] at hh
  apply hh.trans
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro r hr
  change 0 < r at hr
  dsimp only
  rw [abs_of_pos (by positivity : 0 < 2 * r), smul_eq_mul]

theorem integral_square_substitution (g : ℝ → ℝ) :
    (∫ r in Ioi 0, 2 * r * g (r ^ 2)) = ∫ u in Ioi 0, g u := by
  have hh := integral_image_eq_integral_abs_deriv_smul
    (f := fun r : ℝ => r ^ 2) (f' := fun r : ℝ => 2 * r)
    measurableSet_Ioi (fun r _ => (show HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r from
      by simpa using (hasDerivAt_id r).pow 2).hasDerivWithinAt)
    (show InjOn (fun r : ℝ => r ^ 2) (Ioi 0) from
      fun r hr s hs hrs => (sq_eq_sq₀ hr.le hs.le).mp hrs) g
  rw [square_image_Ioi] at hh
  rw [hh]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change 0 < r at hr
  dsimp only
  rw [abs_of_pos (by positivity : 0 < 2 * r), smul_eq_mul]

theorem qed_radial_envelope_integrable {F : ℝ → ℝ}
    (hQ : IntegrableOn (fun u => F u ^ 2) (Ioi 0)) :
    Integrable (fun k : DiracMomentum => F (‖k‖ ^ 2) ^ 2 / ‖k‖ ^ 2) := by
  have hr := ((integrableOn_square_substitution (fun u => F u ^ 2)).mp hQ).const_mul (1 / 2 : ℝ)
  have hr' : IntegrableOn (fun r : ℝ => r * F (r ^ 2) ^ 2) (Ioi 0) := by
    change Integrable (fun r : ℝ => r * F (r ^ 2) ^ 2) (volume.restrict (Ioi 0))
    convert hr using 1
    funext r
    ring
  apply (integrable_fun_norm_addHaar (E := DiracMomentum) volume
    (f := fun r : ℝ => F (r ^ 2) ^ 2 / r ^ 2)).mpr
  apply hr'.congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  field_simp

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
theorem bareWardNumerator_entry_sq_bound (m : ℝ) (k : DiracMomentum) (μ i j : Fin 4) :
    ‖bareWardNumeratorExplicit m k μ i j‖ ^ 2 ≤ ‖k‖ ^ 2 + m ^ 2 := by
  rw [diracMomentum_norm_sq]
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    simp [bareWardNumeratorExplicit, Complex.sq_norm, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im] <;>
    nlinarith [sq_nonneg (k 0), sq_nonneg (k 1), sq_nonneg (k 2),
      sq_nonneg (k 3), sq_nonneg m]

def dressedBareWardEntry (F : ℝ → ℝ) (m : ℝ) (μ i j : Fin 4)
    (k : DiracMomentum) : ℂ := (F (‖k‖ ^ 2) : ℂ) * bareWardLine m k μ i j

set_option maxHeartbeats 2000000 in
theorem dressedBareWardEntry_measurable {F : ℝ → ℝ} (hF : Measurable F)
    (m : ℝ) (μ i j : Fin 4) : Measurable (dressedBareWardEntry F m μ i j) := by
  have hs (a b : Fin 4) : Measurable (fun k : DiracMomentum => diracSlash k a b) := by
    simp only [diracSlash, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun l _ => by fun_prop)
  have hf (a b : Fin 4) : Measurable (fun k : DiracMomentum => freeDiracNumerator m k a b) := by
    simp only [freeDiracNumerator, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact (measurable_const.mul (hs a b)).add measurable_const
  have hn : Measurable (fun k : DiracMomentum => bareWardNumeratorExplicit m k μ i j) := by
    simp_rw [← bareWardNumerator_eq_explicit]
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun l _ => measurable_const.mul (hf l j))
  have heq : dressedBareWardEntry F m μ i j = fun k =>
      (F (‖k‖ ^ 2) : ℂ) *
        (((‖k‖ ^ 2 + m ^ 2 : ℝ) : ℂ)⁻¹ * bareWardNumeratorExplicit m k μ i j) := by
    funext k
    simp only [dressedBareWardEntry, bareWardLine, freeDiracPropagator,
      Matrix.mul_smul, bareWardNumerator_eq_explicit, Matrix.smul_apply, smul_eq_mul]
  rw [heq]
  exact (Complex.measurable_ofReal.comp (hF.comp (by fun_prop))).mul
    ((by fun_prop : Measurable (fun k : DiracMomentum =>
      ((‖k‖ ^ 2 + m ^ 2 : ℝ) : ℂ)⁻¹)).mul hn)

theorem dressedBareWardEntry_sq_bound (F : ℝ → ℝ) (m : ℝ)
    (μ i j : Fin 4) (k : DiracMomentum) (hk : k ≠ 0) :
    ‖dressedBareWardEntry F m μ i j k‖ ^ 2 ≤ F (‖k‖ ^ 2) ^ 2 / ‖k‖ ^ 2 := by
  have hkn : 0 < ‖k‖ := norm_pos_iff.mpr hk
  have hd : 0 < ‖k‖ ^ 2 + m ^ 2 := by positivity
  have hline : bareWardLine m k μ i j =
      ((‖k‖ ^ 2 + m ^ 2 : ℝ) : ℂ)⁻¹ * bareWardNumeratorExplicit m k μ i j := by
    simp only [bareWardLine, freeDiracPropagator, Matrix.mul_smul,
      bareWardNumerator_eq_explicit, Matrix.smul_apply, smul_eq_mul]
  rw [dressedBareWardEntry, norm_mul, hline, norm_mul, mul_pow, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg hd.le, inv_pow]
  rw [← mul_assoc]
  calc
    _ ≤ F (‖k‖ ^ 2) ^ 2 * ((‖k‖ ^ 2 + m ^ 2) ^ 2)⁻¹ * (‖k‖ ^ 2 + m ^ 2) := by
      exact mul_le_mul_of_nonneg_left (bareWardNumerator_entry_sq_bound m k μ i j)
        (by positivity)
    _ = F (‖k‖ ^ 2) ^ 2 / (‖k‖ ^ 2 + m ^ 2) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hkn)
      (by nlinarith [sq_nonneg m])

theorem dressedBareWardEntry_memLp_two {F : ℝ → ℝ} (hF : Measurable F)
    (hQ : IntegrableOn (fun u => F u ^ 2) (Ioi 0)) (m : ℝ) (μ i j : Fin 4) :
    MemLp (dressedBareWardEntry F m μ i j) 2 := by
  have hm : AEStronglyMeasurable (dressedBareWardEntry F m μ i j) volume :=
    (dressedBareWardEntry_measurable hF m μ i j).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (qed_radial_envelope_integrable hQ).mono' (hm.norm.pow 2)
  filter_upwards [(Set.countable_singleton (0 : DiracMomentum)).ae_notMem volume] with k hk
  change ‖‖dressedBareWardEntry F m μ i j k‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact dressedBareWardEntry_sq_bound F m μ i j k (by simpa only [mem_singleton_iff] using hk)

theorem bareWardTensor_eq_entries (F : ℝ → ℝ) (m : ℝ) (Q k : DiracMomentum)
    (μ ν : Fin 4) :
    bareWardTensor F m Q μ ν k =
      ∑ i, ∑ j, dressedBareWardEntry F m μ i j k *
        dressedBareWardEntry F m ν j i (k + Q) := by
  simp only [bareWardTensor, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    dressedBareWardEntry, Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The original tensor is absolutely integrable for every external momentum;
the mass may vanish. No tensor-integrability premise is used. -/
theorem bareWardTensor_integrable_of_square {F : ℝ → ℝ} (hF : Measurable F)
    (hQ : IntegrableOn (fun u => F u ^ 2) (Ioi 0))
    (m : ℝ) (Q : DiracMomentum) (μ ν : Fin 4) :
    Integrable (bareWardTensor F m Q μ ν) := by
  have hi : Integrable (fun k => ∑ i, ∑ j,
      dressedBareWardEntry F m μ i j k * dressedBareWardEntry F m ν j i (k + Q)) :=
    integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ =>
      memLp_two_mul_translate_integrable (dressedBareWardEntry_memLp_two hF hQ m μ i j)
        (dressedBareWardEntry_memLp_two hF hQ m ν j i) Q))
  exact hi.congr (Eventually.of_forall (fun k => (bareWardTensor_eq_entries F m Q k μ ν).symm))

theorem bareWardPolarization_continuous_of_square {F : ℝ → ℝ} (hF : Measurable F)
    (hQ : IntegrableOn (fun u => F u ^ 2) (Ioi 0))
    (m e : ℝ) (μ ν : Fin 4) :
    Continuous (fun Q => bareWardPolarization F m e Q μ ν) := by
  have heq (Q : DiracMomentum) : (∫ k, bareWardTensor F m Q μ ν k) =
      ∑ i, ∑ j, ∫ k,
        dressedBareWardEntry F m μ i j k * dressedBareWardEntry F m ν j i (k + Q) := by
    simp_rw [bareWardTensor_eq_entries]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _
      exact integral_finset_sum _ (fun j _ =>
        memLp_two_mul_translate_integrable (dressedBareWardEntry_memLp_two hF hQ m μ i j)
          (dressedBareWardEntry_memLp_two hF hQ m ν j i) Q)
    · intro i _
      exact integrable_finset_sum _ (fun j _ =>
        memLp_two_mul_translate_integrable (dressedBareWardEntry_memLp_two hF hQ m μ i j)
          (dressedBareWardEntry_memLp_two hF hQ m ν j i) Q)
  have hc : Continuous (fun Q : DiracMomentum => ∑ i, ∑ j, ∫ k,
      dressedBareWardEntry F m μ i j k * dressedBareWardEntry F m ν j i (k + Q)) :=
    continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ =>
      memLp_two_correlation_continuous (dressedBareWardEntry_memLp_two hF hQ m μ i j)
        (dressedBareWardEntry_memLp_two hF hQ m ν j i)))
  apply continuous_const.mul (hc.congr (fun Q => (heq Q).symm))

def qedKappa (F : ℝ → ℝ) (m e : ℝ) : ℝ :=
  e ^ 2 / (8 * Real.pi ^ 2) * ∫ u in Ioi 0,
    (u * (u + 2 * m ^ 2) / (u + m ^ 2) ^ 2) * F u ^ 2

theorem qedKappa_density_bounds (m : ℝ) {u : ℝ} (hu : 0 < u) :
    0 < u * (u + 2 * m ^ 2) / (u + m ^ 2) ^ 2 ∧
      u * (u + 2 * m ^ 2) / (u + m ^ 2) ^ 2 ≤ 1 := by
  have hd : 0 < u + m ^ 2 := by positivity
  constructor
  · positivity
  · apply (div_le_one (sq_pos_of_pos hd)).mpr
    nlinarith [sq_nonneg (m ^ 2)]

theorem qedKappa_density_integrable {F : ℝ → ℝ} (hF : Measurable F)
    (hQ : IntegrableOn (fun u => F u ^ 2) (Ioi 0)) (m : ℝ) :
    IntegrableOn (fun u => (u * (u + 2 * m ^ 2) / (u + m ^ 2) ^ 2) * F u ^ 2) (Ioi 0) := by
  apply hQ.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_of_nonneg (mul_nonneg (qedKappa_density_bounds m hu).1.le (sq_nonneg _))]
  exact mul_le_of_le_one_left (sq_nonneg _) (qedKappa_density_bounds m hu).2

theorem qed_mass_weight_integrable {F : ℝ → ℝ} (hF : Measurable F)
    (hQ : IntegrableOn (fun u => F u ^ 2) (Ioi 0)) (m : ℝ) :
    Integrable (fun k : DiracMomentum => F (‖k‖ ^ 2) ^ 2 / (‖k‖ ^ 2 + m ^ 2)) := by
  apply (qed_radial_envelope_integrable hQ).mono'
    (by apply Measurable.aestronglyMeasurable; fun_prop)
  filter_upwards [(Set.countable_singleton (0 : DiracMomentum)).ae_notMem volume] with k hk
  have hkn : 0 < ‖k‖ := norm_pos_iff.mpr (by simpa only [mem_singleton_iff] using hk)
  rw [Real.norm_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hkn) (by nlinarith [sq_nonneg m])

theorem qed_coordinate_weight_integrable {F : ℝ → ℝ} (hF : Measurable F)
    (hQ : IntegrableOn (fun u => F u ^ 2) (Ioi 0)) (m : ℝ) :
    Integrable (fun k : DiracMomentum =>
      ‖k‖ ^ 2 * (F (‖k‖ ^ 2) ^ 2 / (‖k‖ ^ 2 + m ^ 2) ^ 2)) := by
  apply (qed_radial_envelope_integrable hQ).mono' (by fun_prop)
  filter_upwards [(Set.countable_singleton (0 : DiracMomentum)).ae_notMem volume] with k hk
  have hkn : 0 < ‖k‖ := norm_pos_iff.mpr (by simpa only [mem_singleton_iff] using hk)
  have hd : 0 < ‖k‖ ^ 2 + m ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity), ← mul_div_assoc]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos hkn)).mpr
  have hs : (‖k‖ ^ 2) ^ 2 ≤ (‖k‖ ^ 2 + m ^ 2) ^ 2 := by nlinarith [sq_nonneg m]
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg (F (‖k‖ ^ 2)))
  nlinarith

theorem qed_zero_density_integrable {F : ℝ → ℝ} (hF : Measurable F)
    (hQ : IntegrableOn (fun u => F u ^ 2) (Ioi 0)) (m : ℝ) :
    Integrable (fun k : DiracMomentum =>
      (‖k‖ ^ 2 + 2 * m ^ 2) * F (‖k‖ ^ 2) ^ 2 / (‖k‖ ^ 2 + m ^ 2) ^ 2) := by
  have hh := ((qed_mass_weight_integrable hF hQ m).const_mul 2).sub
    (qed_coordinate_weight_integrable hF hQ m)
  apply hh.congr
  filter_upwards [(Set.countable_singleton (0 : DiracMomentum)).ae_notMem volume] with k hk
  have hkn : 0 < ‖k‖ := norm_pos_iff.mpr (by simpa only [mem_singleton_iff] using hk)
  have hd : ‖k‖ ^ 2 + m ^ 2 ≠ 0 := by positivity
  change 2 * (F (‖k‖ ^ 2) ^ 2 / (‖k‖ ^ 2 + m ^ 2)) -
      ‖k‖ ^ 2 * (F (‖k‖ ^ 2) ^ 2 / (‖k‖ ^ 2 + m ^ 2) ^ 2) =
    (‖k‖ ^ 2 + 2 * m ^ 2) * F (‖k‖ ^ 2) ^ 2 / (‖k‖ ^ 2 + m ^ 2) ^ 2
  field_simp
  ring

theorem qedKappa_momentum_formula (F : ℝ → ℝ) (m e : ℝ) :
    qedKappa F m e = 2 * e ^ 2 * (2 * Real.pi) ^ (-4 : ℤ) *
      ∫ k : DiracMomentum,
        (‖k‖ ^ 2 + 2 * m ^ 2) * F (‖k‖ ^ 2) ^ 2 / (‖k‖ ^ 2 + m ^ 2) ^ 2 := by
  have hp := fourier_radial_integral (fun r =>
    (r ^ 2 + 2 * m ^ 2) * F (r ^ 2) ^ 2 / (r ^ 2 + m ^ 2) ^ 2)
  have hs := integral_square_substitution (fun u =>
    (u * (u + 2 * m ^ 2) / (u + m ^ 2) ^ 2) * F u ^ 2)
  have hs' : (∫ u in Ioi 0,
      (u * (u + 2 * m ^ 2) / (u + m ^ 2) ^ 2) * F u ^ 2) =
      2 * ∫ r in Ioi 0,
        r ^ 3 * ((r ^ 2 + 2 * m ^ 2) * F (r ^ 2) ^ 2 / (r ^ 2 + m ^ 2) ^ 2) := by
    rw [← hs, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp only
    ring
  unfold qedKappa
  rw [hs']
  have hps := congrArg (fun x : ℝ => 2 * e ^ 2 * x) hp
  convert hps.symm using 1 <;> ring

/-- The exact zero-transfer tensor, derived from the literal Clifford trace
and volume-preserving coordinate symmetries. -/
theorem bareWardPolarization_zero {F : ℝ → ℝ} (hF : Measurable F)
    (hQ : IntegrableOn (fun u => F u ^ 2) (Ioi 0))
    (m e : ℝ) (μ ν : Fin 4) :
    bareWardPolarization F m e 0 μ ν =
      (qedKappa F m e : ℂ) * (if μ = ν then 1 else 0) := by
  let g : ℝ → ℝ := fun u => F u ^ 2 / (u + m ^ 2) ^ 2
  let h : DiracMomentum → ℝ := fun k => F (‖k‖ ^ 2) ^ 2 / (‖k‖ ^ 2 + m ^ 2)
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hw := qed_coordinate_weight_integrable hF hQ m
  have hc := radial_coordinate_product_integrable hg hw μ ν
  have hh := qed_mass_weight_integrable hF hQ m
  have heq : (∫ k, bareWardTensor F m 0 μ ν k) =
      ((8 * (∫ k : DiracMomentum, k μ * k ν * g (‖k‖ ^ 2)) -
        4 * (if μ = ν then 1 else 0) * ∫ k, h k : ℝ) : ℂ) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub (hc.const_mul 8) (hh.const_mul (4 * (if μ = ν then 1 else 0))),
      ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [(Set.countable_singleton (0 : DiracMomentum)).ae_notMem volume] with k hk
    have hkn : 0 < ‖k‖ := norm_pos_iff.mpr (by simpa only [mem_singleton_iff] using hk)
    have hd : ((‖k‖ ^ 2 + m ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by positivity)
    simp only [bareWardTensor, add_zero, bareWardLine_cross_trace]
    dsimp [g, h]
    push_cast
    field_simp
  have hav := (radial_coordinate_average hg hw μ ν).2
  have hz : (∫ k : DiracMomentum,
      (‖k‖ ^ 2 + 2 * m ^ 2) * F (‖k‖ ^ 2) ^ 2 / (‖k‖ ^ 2 + m ^ 2) ^ 2) =
      2 * (∫ k, h k) - ∫ k : DiracMomentum, ‖k‖ ^ 2 * g (‖k‖ ^ 2) := by
    rw [← integral_const_mul, ← integral_sub (hh.const_mul 2) hw]
    apply integral_congr_ae
    filter_upwards [(Set.countable_singleton (0 : DiracMomentum)).ae_notMem volume] with k hk
    have hkn : 0 < ‖k‖ := norm_pos_iff.mpr (by simpa only [mem_singleton_iff] using hk)
    have hd : ‖k‖ ^ 2 + m ^ 2 ≠ 0 := by positivity
    change (‖k‖ ^ 2 + 2 * m ^ 2) * F (‖k‖ ^ 2) ^ 2 / (‖k‖ ^ 2 + m ^ 2) ^ 2 =
      2 * (F (‖k‖ ^ 2) ^ 2 / (‖k‖ ^ 2 + m ^ 2)) -
        ‖k‖ ^ 2 * (F (‖k‖ ^ 2) ^ 2 / (‖k‖ ^ 2 + m ^ 2) ^ 2)
    field_simp
    ring
  rw [bareWardPolarization, heq, hav, qedKappa_momentum_formula, hz]
  split_ifs <;> push_cast <;> ring

theorem qedKappa_pos {F : ℝ → ℝ} (hF : Measurable F)
    (hQ : IntegrableOn (fun u => F u ^ 2) (Ioi 0))
    (hpos : ∀ u > 0, 0 < F u) (m : ℝ) {e : ℝ} (he : e ≠ 0) :
    0 < qedKappa F m e := by
  have hi := qedKappa_density_integrable hF hQ m
  have hnonneg : ∀ᵐ u ∂volume.restrict (Ioi 0),
      0 ≤ (u * (u + 2 * m ^ 2) / (u + m ^ 2) ^ 2) * F u ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (qedKappa_density_bounds m hu).1.le (sq_nonneg _)
  have hs : Ioi (0 : ℝ) ⊆ Function.support (fun u =>
      (u * (u + 2 * m ^ 2) / (u + m ^ 2) ^ 2) * F u ^ 2) := by
    intro u hu
    exact ne_of_gt (mul_pos (qedKappa_density_bounds m hu).1 (sq_pos_of_pos (hpos u hu)))
  have hm : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioi 0) := by simp
  have hp := (integral_pos_iff_support_of_nonneg_ae hnonneg hi).mpr
    (hm.trans_le (measure_mono hs))
  exact mul_pos (div_pos (sq_pos_of_ne_zero he) (by positivity)) hp

theorem qedKappa_massless (F : ℝ → ℝ) (e : ℝ) :
    qedKappa F 0 e = e ^ 2 / (8 * Real.pi ^ 2) * ∫ u in Ioi 0, F u ^ 2 := by
  unfold qedKappa
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change 0 < u at hu
  dsimp only
  norm_num
  field_simp

theorem wardLaplaceKernel_pos (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (hρ : ρ ≠ 0) (a u : ℝ) :
    0 < wardLaplaceKernel ρ a u := by
  letI : NeZero ρ := ⟨hρ⟩
  exact integral_exp_pos (nonnegative_laplace_integrable ρ hp
    (mul_nonneg (sq_nonneg a) (le_max_right u 0)))

open Asymptotics in
theorem continuous_tensor_contraction_small {T : DiracMomentum → Fin 4 → Fin 4 → ℂ}
    (hT : ∀ μ ν, Continuous (fun Q => T Q μ ν)) {κ : ℝ}
    (h0 : ∀ μ ν, T 0 μ ν = (κ : ℂ) * (if μ = ν then 1 else 0)) (ν : Fin 4) :
    (fun Q => (∑ μ, (Q μ : ℂ) * T Q μ ν) - (κ : ℂ) * (Q ν : ℂ))
      =o[𝓝 (0 : DiracMomentum)] (fun Q => ‖Q‖) := by
  have ho (μ : Fin 4) : (fun Q : DiracMomentum =>
      (Q μ : ℂ) * (T Q μ ν - T 0 μ ν)) =o[𝓝 0] (fun Q => ‖Q‖) := by
    have hc : (fun Q : DiracMomentum => (Q μ : ℂ)) =O[𝓝 0] (fun Q => ‖Q‖) := by
      apply isBigO_of_le
      intro Q
      simpa only [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg Q)]
        using PiLp.norm_apply_le Q μ
    have hd : (fun Q : DiracMomentum => T Q μ ν - T 0 μ ν) =o[𝓝 0] (fun _ => (1 : ℝ)) :=
      (isLittleO_const_iff (by norm_num : (1 : ℝ) ≠ 0)).mpr
        (by simpa only [sub_self] using ((hT μ ν).tendsto 0).sub_const (T 0 μ ν))
    simpa only [mul_one] using hc.mul_isLittleO hd
  have hh := IsLittleO.sum (s := Finset.univ) (fun μ _ => ho μ)
  apply hh.congr_left (fun Q => ?_)
  simp_rw [mul_sub, Finset.sum_sub_distrib, h0]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem bareWardPolarization_small_momentum {F : ℝ → ℝ} (hF : Measurable F)
    (hQ : IntegrableOn (fun u => F u ^ 2) (Ioi 0))
    (m e : ℝ) (ν : Fin 4) :
    (fun Q => (∑ μ, (Q μ : ℂ) * bareWardPolarization F m e Q μ ν) -
        (qedKappa F m e : ℂ) * (Q ν : ℂ))
      =o[𝓝 (0 : DiracMomentum)] (fun Q => ‖Q‖) :=
  continuous_tensor_contraction_small
    (bareWardPolarization_continuous_of_square hF hQ m e)
    (bareWardPolarization_zero hF hQ m e) ν

def bareWardPolarizationIntegrand (F : ℝ → ℝ) (m e : ℝ) (Q : DiracMomentum)
    (μ ν : Fin 4) (k : DiracMomentum) : ℂ :=
  ((-(e ^ 2) * (2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) * bareWardTensor F m Q μ ν k

theorem bareWardPolarization_eq_integral (F : ℝ → ℝ) (m e : ℝ)
    (Q : DiracMomentum) (μ ν : Fin 4) :
    bareWardPolarization F m e Q μ ν =
      ∫ k, bareWardPolarizationIntegrand F m e Q μ ν k := by
  simp only [bareWardPolarization, bareWardPolarizationIntegrand, integral_const_mul]

theorem bareWardPolarizationIntegrand_integrable_of_square {F : ℝ → ℝ} (hF : Measurable F)
    (hQ : IntegrableOn (fun u => F u ^ 2) (Ioi 0))
    (m e : ℝ) (Q : DiracMomentum) (μ ν : Fin 4) :
    Integrable (bareWardPolarizationIntegrand F m e Q μ ν) :=
  (bareWardTensor_integrable_of_square hF hQ m Q μ ν).const_mul _

theorem bareWardTensor_integrable_of_original {F : ℝ → ℝ} (m : ℝ)
    {e : ℝ} (he : e ≠ 0) (Q : DiracMomentum) (μ ν : Fin 4)
    (hH : Integrable (bareWardPolarizationIntegrand F m e Q μ ν)) :
    Integrable (bareWardTensor F m Q μ ν) := by
  have hc : ((-(e ^ 2) * (2 * Real.pi) ^ (-4 : ℤ) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 he))
      (zpow_ne_zero _ (by positivity)))
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _).mp hH

/-- Forward part of the exact one-loop criterion, for every finite nonzero
positive Laplace law. This includes the literal massless free tensor. -/
theorem laplace_general_qed_obstruction (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (hρ : ρ ≠ 0) (a m e : ℝ)
    (hQ : IntegrableOn (fun u => wardLaplaceKernel ρ a u ^ 2) (Ioi 0)) :
    (∀ Q μ ν, Integrable (bareWardPolarizationIntegrand (wardLaplaceKernel ρ a) m e Q μ ν)) ∧
    (∀ μ ν, Continuous (fun Q => bareWardPolarization (wardLaplaceKernel ρ a) m e Q μ ν)) ∧
    (∀ μ ν, bareWardPolarization (wardLaplaceKernel ρ a) m e 0 μ ν =
      (qedKappa (wardLaplaceKernel ρ a) m e : ℂ) * (if μ = ν then 1 else 0)) ∧
    (∀ ν, (fun Q => (∑ μ, (Q μ : ℂ) * bareWardPolarization (wardLaplaceKernel ρ a) m e Q μ ν) -
      (qedKappa (wardLaplaceKernel ρ a) m e : ℂ) * (Q ν : ℂ))
      =o[𝓝 (0 : DiracMomentum)] (fun Q => ‖Q‖)) ∧
    (e ≠ 0 → 0 < qedKappa (wardLaplaceKernel ρ a) m e) := by
  have hF := (wardLaplaceKernel_continuous ρ hp a).measurable
  exact ⟨bareWardPolarizationIntegrand_integrable_of_square hF hQ m e,
    bareWardPolarization_continuous_of_square hF hQ m e,
    bareWardPolarization_zero hF hQ m e, bareWardPolarization_small_momentum hF hQ m e,
    fun he => qedKappa_pos hF hQ (fun u _ => wardLaplaceKernel_pos ρ hp hρ a u) m he⟩

/-- The converse applies at any one real external momentum and to the
literal charged, Fourier-normalized tensor, with nonzero charge. -/
theorem laplace_qed_square_integrable_of_original (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (a : ℝ) {m e : ℝ} (hm : 0 ≤ m) (he : e ≠ 0)
    (Q : DiracMomentum)
    (hH : ∀ μ ν, Integrable (bareWardPolarizationIntegrand (wardLaplaceKernel ρ a) m e Q μ ν)) :
    IntegrableOn (fun u => wardLaplaceKernel ρ a u ^ 2) (Ioi 0) :=
  wardLaplaceKernel_square_integrable_of_tensor ρ hp a hm Q
    (fun μ ν => bareWardTensor_integrable_of_original m he Q μ ν (hH μ ν))

theorem laplace_qed_integrable_iff (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (a : ℝ) {m e : ℝ} (hm : 0 ≤ m) (he : e ≠ 0)
    (Q : DiracMomentum) :
    (∀ μ ν, Integrable (bareWardPolarizationIntegrand (wardLaplaceKernel ρ a) m e Q μ ν)) ↔
      IntegrableOn (fun u => wardLaplaceKernel ρ a u ^ 2) (Ioi 0) := by
  constructor
  · exact laplace_qed_square_integrable_of_original ρ hp a hm he Q
  · intro hQ
    exact bareWardPolarizationIntegrand_integrable_of_square
      (wardLaplaceKernel_continuous ρ hp a).measurable hQ m e Q

/-- Named source proposition `prop:QED-general-obstruction`: the exact
criterion, actual tensor convergence and continuity, its positive isotropic
zero-momentum value, and the resulting first-order Ward obstruction. -/
theorem qed_general_obstruction (ρ : Measure ℝ) [IsFiniteMeasure ρ]
    (hp : ∀ᵐ τ ∂ρ, 0 ≤ τ) (hρ : ρ ≠ 0) (a : ℝ) {m e : ℝ}
    (hm : 0 ≤ m)
    (hQ : IntegrableOn (fun u => wardLaplaceKernel ρ a u ^ 2) (Ioi 0)) :
    (∀ Q μ ν, Integrable (bareWardPolarizationIntegrand (wardLaplaceKernel ρ a) m e Q μ ν)) ∧
    (∀ μ ν, Continuous (fun Q => bareWardPolarization (wardLaplaceKernel ρ a) m e Q μ ν)) ∧
    (∀ μ ν, bareWardPolarization (wardLaplaceKernel ρ a) m e 0 μ ν =
      (qedKappa (wardLaplaceKernel ρ a) m e : ℂ) * (if μ = ν then 1 else 0)) ∧
    (∀ ν, (fun Q => (∑ μ, (Q μ : ℂ) * bareWardPolarization (wardLaplaceKernel ρ a) m e Q μ ν) -
      (qedKappa (wardLaplaceKernel ρ a) m e : ℂ) * (Q ν : ℂ))
      =o[𝓝 (0 : DiracMomentum)] (fun Q => ‖Q‖)) ∧
    (e ≠ 0 → 0 < qedKappa (wardLaplaceKernel ρ a) m e) ∧
    (e ≠ 0 → ∀ Q, (∀ μ ν, Integrable (bareWardPolarizationIntegrand (wardLaplaceKernel ρ a) m e Q μ ν)) ↔
      IntegrableOn (fun u => wardLaplaceKernel ρ a u ^ 2) (Ioi 0)) := by
  obtain ⟨hI, hC, hZ, hS, hP⟩ := laplace_general_qed_obstruction ρ hp hρ a m e hQ
  exact ⟨hI, hC, hZ, hS, hP, fun he Q => laplace_qed_integrable_iff ρ hp a hm he Q⟩

end UV
