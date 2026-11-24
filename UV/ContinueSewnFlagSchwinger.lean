import UV.ContinueSewnFlagFourier
import UV.ContinueSewnFlagSectors

/-! The original massive affine denominators and their joint positive
Schwinger representation, with the exact Gamma normalizations. -/

noncomputable section
open Real MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal Matrix
namespace UV.SewnFlags

def routedDenominator {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (ν m : Fin N → ℝ) (p : Fin N → ScalarMomentum)
    (k : EuclideanSpace ℝ (Fin L × Fin 4)) :=
  ∏ i, ((m i)^2 + ‖residualRouting C i k + p i‖^2)^(-ν i)

def routedTimePower {N : ℕ} (ν m t : Fin N → ℝ) :=
  (∏ i, t i^(ν i-1)) * exp (-(∑ i, (m i)^2*t i))

theorem routedTimePower_nonneg {N : ℕ} (ν m t : Fin N → ℝ) (ht : t ∈ positiveDurations N) :
    0 ≤ routedTimePower ν m t :=
  mul_nonneg (Finset.prod_nonneg fun i _ => rpow_nonneg (ht i).le _) (exp_pos _).le

theorem routedAffineEnergy_continuous {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (p : Fin N → ScalarMomentum) :
    Continuous (fun x : (Fin N → ℝ) × EuclideanSpace ℝ (Fin L × Fin 4) =>
      routedAffineEnergy C x.1 p x.2) := by
  unfold routedAffineEnergy
  exact continuous_finset_sum _ fun i _ => ((continuous_apply i).comp continuous_fst).mul
    ((((residualRouting C i).continuous.comp continuous_snd).add continuous_const).norm.pow 2)

private theorem routed_line_schwinger {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^(a-1)*exp (-(r*t)))) =
      ENNReal.ofReal (Gamma a*r^(-a)) := by
  have hI : IntegrableOn (fun t : ℝ => t^(a-1)*exp (-(r*t))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a-1) (b := r)
      (by linarith [ha]) le_rfl hr
    simpa only [rpow_one,neg_mul] using h
  have h0 : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun t => t^(a-1)*exp (-(r*t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (rpow_nonneg ht.le _) (exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hI h0,integral_rpow_mul_exp_neg_mul_Ioi ha hr,
    one_div,inv_rpow hr.le,← rpow_neg hr.le,mul_comm]

theorem positiveDurations_measure {N : ℕ} :
    (volume : Measure (Fin N → ℝ)).restrict (positiveDurations N) =
      Measure.pi (fun _ : Fin N => volume.restrict (Ioi (0:ℝ))) := by
  have he : positiveDurations N = univ.pi (fun _ : Fin N => Ioi (0:ℝ)) := by
    ext t
    simp [positiveDurations]
  rw [volume_pi,he,Measure.restrict_pi_pi]

/-- Positive Tonelli retains the full correlated momentum
characteristic and every individual affine line in the denominator. -/
theorem routed_schwinger_identity {N L : ℕ} (C : Matrix (Fin N) (Fin L) ℝ)
    (ν m : Fin N → ℝ) (hν : ∀ i, 0 < ν i) (hm : ∀ i, 0 < (m i)^2) (p : Fin N → ScalarMomentum)
    (g : EuclideanSpace ℝ (Fin L × Fin 4) → ℝ≥0∞) (hg : Measurable g) :
    ENNReal.ofReal (∏ i, Gamma (ν i)) *
        (∫⁻ k, g k*ENNReal.ofReal (routedDenominator C ν m p k)) =
      ∫⁻ t in positiveDurations N, ENNReal.ofReal (routedTimePower ν m t) *
        ∫⁻ k, g k*ENNReal.ofReal (exp (-(routedAffineEnergy C t p k))) := by
  let τ := (volume : Measure (Fin N → ℝ)).restrict (positiveDurations N)
  let V := EuclideanSpace ℝ (Fin L × Fin 4)
  let D := fun (k : V) i => (m i)^2 + ‖residualRouting C i k + p i‖^2
  have hD (k : V) (i : Fin N) : 0 < D k i :=
    add_pos_of_pos_of_nonneg (hm i) (sq_nonneg _)
  let f := fun (t : Fin N → ℝ) (k : V) => g k * ∏ i, ENNReal.ofReal (t i^(ν i-1)*exp (-(D k i*t i)))
  have hf : Measurable (fun q : (Fin N → ℝ) × V => f q.1 q.2) := by
    have ht (i : Fin N) : Measurable (fun q : (Fin N → ℝ) × V => q.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    have hD' (i : Fin N) : Measurable (fun q : (Fin N → ℝ) × V => D q.2 i) :=
      (continuous_const.add ((((residualRouting C i).continuous.comp continuous_snd).add continuous_const).norm.pow 2)).measurable
    exact (hg.comp measurable_snd).mul
      (Finset.measurable_prod _ fun i _ =>
        ((ht i).pow_const _ |>.mul (((hD' i).mul (ht i)).neg.exp)).ennreal_ofReal)
  calc
    _ = ∫⁻ k : V, ∫⁻ t, f t k ∂τ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro k
      have h (i : Fin N) : Measurable (fun t : ℝ => ENNReal.ofReal (t^(ν i-1)*exp (-(D k i*t)))) :=
        ((measurable_id.pow_const _).mul ((measurable_id.const_mul _).neg.exp)).ennreal_ofReal
      change _ = ∫⁻ t, g k * ∏ i, (fun r : ℝ => ENNReal.ofReal (r^(ν i-1)*exp (-(D k i*r)))) (t i) ∂τ
      have hP : Measurable (fun t : Fin N → ℝ => ∏ i, ENNReal.ofReal (t i^(ν i-1)*exp (-(D k i*t i)))) :=
        Finset.measurable_prod _ (fun i _ => (h i).comp (measurable_pi_apply i))
      rw [lintegral_const_mul _ hP]
      dsimp only [τ]
      rw [positiveDurations_measure,network_lintegral_fintype_prod _ _ h]
      simp_rw [routed_line_schwinger (hν _) (hD _ _),ENNReal.ofReal_mul (Gamma_pos_of_pos (hν _)).le]
      rw [Finset.prod_mul_distrib,← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Gamma_pos_of_pos (hν i)).le),
        ← ENNReal.ofReal_prod_of_nonneg (fun i _ => rpow_nonneg (hD k i).le _)]
      change _ * (g k * _) = g k * (_ * _)
      ac_rfl
    _ = ∫⁻ t, ∫⁻ k : V, f t k ∂volume ∂τ := (lintegral_lintegral_swap hf.aemeasurable).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (positiveDurations_measurable N)] with t ht
      have h0 (i : Fin N) : 0 ≤ t i^(ν i-1) := rpow_nonneg (ht i).le _
      have he (k : V) : f t k = ENNReal.ofReal (routedTimePower ν m t) *
          (g k * ENNReal.ofReal (exp (-(routedAffineEnergy C t p k)))) := by
        unfold f routedTimePower routedAffineEnergy
        simp_rw [ENNReal.ofReal_mul (h0 _)]
        rw [Finset.prod_mul_distrib,← ENNReal.ofReal_prod_of_nonneg (fun i _ => h0 i),
          ← ENNReal.ofReal_prod_of_nonneg (fun _ _ => exp_nonneg _),
          ← exp_sum,Finset.sum_neg_distrib,
          ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => h0 i)]
        have hDsum : (∑ i, D k i*t i) = (∑ i, (m i)^2*t i) +
            ∑ i, t i*‖residualRouting C i k + p i‖^2 := by
          have hterm (i : Fin N) : D k i*t i =
              (m i)^2*t i + t i*‖residualRouting C i k + p i‖^2 := by
            unfold D
            ring
          simp_rw [hterm, Finset.sum_add_distrib]
        rw [hDsum,neg_add,exp_add,ENNReal.ofReal_mul (exp_nonneg _)]
        ac_rfl
      simp_rw [he]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end UV.SewnFlags
