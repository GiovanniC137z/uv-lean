import UV.AdvanceNetworkTime

/-! Joint integration of the routed marked coefficient with fixed polynomial
powers in momentum and the positive durations, in the intrinsic Euclidean
sector-plane frame. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace UV

/-- Actual iterated, normalized absolute integral after performing the
coherent shared-vertex Fourier integral. -/
def networkRoutedPolynomialCost {E : Type*} [Fintype E] {n L : ℕ}
    (src dst : E → Option (Fin n)) (m z : E → ℝ)
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (b : NetworkVisitSpace n)
    (D : ℝ) (p q : ℕ) : ℝ≥0∞ :=
  ∫⁻ s : E → ℝ, ∫⁻ k : NetworkVisitSpace L, ENNReal.ofReal
    ((∏ e, networkTimePolynomial p q (s e)) * ((1 / (2 * Real.pi) ^ (4 * L)) *
      ((1 + ‖k‖ ^ D) * ‖networkRoutedFourier src dst m z s B b k‖)))
    ∂volume ∂Measure.pi (fun _ : E => volume.restrict (Ioi (0 : ℝ)))

private theorem networkTime_product_one_le {E : Type*} {s : Finset E} {f : E → ℝ}
    (hf : ∀ e ∈ s, 1 ≤ f e) : 1 ≤ ∏ e ∈ s, f e := by
  simpa only [Finset.prod_const_one] using
    Finset.prod_le_prod (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) hf

private theorem networkTime_single_le_product {E : Type*} [Fintype E] (f : E → ℝ)
    (hf : ∀ e, 1 ≤ f e) (e : E) : f e ≤ ∏ i, f i := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ e)]
  exact le_mul_of_one_le_right (zero_le_one.trans (hf e))
    (networkTime_product_one_le (fun i _ => hf i))

private theorem networkRoutedTimeEnvelope {E : Type*} [Fintype E] {n L : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (hB : Function.Injective B)
    (R : ℝ) {D : ℝ} (hD : 0 ≤ D) (p q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m z s : E → ℝ), (∀ e, 0 < s e) →
      ∀ (b : NetworkVisitSpace n), ‖b‖ ≤ R →
      (∫⁻ k : NetworkVisitSpace L, ENNReal.ofReal
        ((∏ e, networkTimePolynomial p q (s e)) * ((1 / (2 * Real.pi) ^ (4 * L)) *
          ((1 + ‖k‖ ^ D) * ‖networkRoutedFourier src dst m z s B b k‖)))) ≤
      ENNReal.ofReal K * ∏ e, ENNReal.ofReal
        (networkTimePolynomial (p + 2 * n) (q + (⌈D⌉₊ + 4 * L)) (s e) *
          networkHeatFive (m e) (z e) (s e)) := by
  obtain ⟨K, hK, hcost⟩ :=
    networkRoutedFourier_weighted_duration_bound G src dst hG hcover B hB R hD
  let N := ⌈D⌉₊ + 4 * L
  refine ⟨K * (2 : ℝ) ^ N, by positivity, ?_⟩
  intro m z s hs b hb
  let T := ∏ e : E, (1 + s e)
  let V := ∏ e : E, (1 + (s e)⁻¹)
  let M := ∏ e, networkTimePolynomial p q (s e)
  have hTV (e : E) : 1 ≤ 1 + s e ∧ 1 ≤ 1 + (s e)⁻¹ :=
    ⟨le_add_of_nonneg_right (hs e).le, le_add_of_nonneg_right (inv_nonneg.mpr (hs e).le)⟩
  have hT : 1 ≤ T := networkTime_product_one_le (fun e _ => (hTV e).1)
  have hV : 1 ≤ V := networkTime_product_one_le (fun e _ => (hTV e).2)
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hV0 : 0 < V := zero_lt_one.trans_le hV
  have hTP (a b : ℕ) (e : E) : 0 ≤ networkTimePolynomial a b (s e) := by
    unfold networkTimePolynomial
    exact mul_nonneg (pow_nonneg (zero_le_one.trans (hTV e).1) _)
      (pow_nonneg (zero_le_one.trans (hTV e).2) _)
  have hM : 0 ≤ M := Finset.prod_nonneg fun e _ => hTP p q e
  have hbox (e : E) : V⁻¹ ≤ s e ∧ s e ≤ T := by
    have h₁ := networkTime_single_le_product (fun i => 1 + (s i)⁻¹) (fun i => (hTV i).2) e
    have h₂ := networkTime_single_le_product (fun i => 1 + s i) (fun i => (hTV i).1) e
    exact ⟨by
      have hh : (s e)⁻¹ ≤ V := (le_add_of_nonneg_left zero_le_one).trans h₁
      simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (hs e)) hh,
      (le_add_of_nonneg_left zero_le_one).trans h₂⟩
  have hf := hcost m z s V⁻¹ T (inv_pos.mpr hV0) hT0 hbox b hb
  have hnon (e : E) :
      0 ≤ networkTimePolynomial (p + 2 * n) (q + N) (s e) * networkHeatFive (m e) (z e) (s e) := by
    exact mul_nonneg (hTP (p + 2 * n) (q + N) e) (networkHeatFive_nonneg (hs e).le _ _)
  have hnorm : 0 ≤ (1 : ℝ) / (2 * Real.pi) ^ (4 * L) := by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal ((hf.1.const_mul _).const_mul M)
    (Eventually.of_forall fun k => mul_nonneg hM (mul_nonneg hnorm
      (mul_nonneg (by positivity : 0 ≤ 1 + ‖k‖ ^ D) (norm_nonneg _)))),
    integral_const_mul, integral_const_mul]
  have hVN : (1 + V⁻¹⁻¹) ^ N ≤ (2 * V) ^ N := by
    rw [inv_inv]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hV]) _
  have hUpper :
      M * (K * networkSharedPrefactor m z s * T ^ (2 * n) * (1 + V⁻¹⁻¹) ^ N) ≤
        (K * (2 : ℝ) ^ N) * (∏ e, networkTimePolynomial (p + 2 * n) (q + N) (s e) *
          networkHeatFive (m e) (z e) (s e)) := by
    calc
      _ ≤ M * (K * networkSharedPrefactor m z s * T ^ (2 * n) * (2 * V) ^ N) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVN (by
          have hp := networkSharedPrefactor_nonneg m z s hs
          positivity)) hM
      _ = (K * (2 : ℝ) ^ N) * (M * networkSharedPrefactor m z s * T ^ (2 * n) * V ^ N) := by
        rw [mul_pow]
        ring
      _ = _ := by
        unfold M networkSharedPrefactor T V
        rw [← Finset.prod_pow, ← Finset.prod_pow,
          ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        congr 1
        apply Finset.prod_congr rfl
        intro e _
        unfold networkTimePolynomial
        rw [pow_add, pow_add]
        ring
  rw [← ENNReal.ofReal_prod_of_nonneg (fun e _ => hnon e),
    ← ENNReal.ofReal_mul (show 0 ≤ K * (2 : ℝ) ^ N by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_left hf.2 hM).trans hUpper

/-- The joint routed momentum and proper-time cost has a finite inverse
power bound when all masses are positive and all transverse marks have
a common strictly positive lower scale. -/
theorem networkRoutedPolynomialCost_bound {E : Type*} [Fintype E] {n L : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (m c : E → ℝ) (hm : ∀ e, 0 < m e) (hc : ∀ e, 0 < c e)
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (hB : Function.Injective B)
    (R : ℝ) {D : ℝ} (hD : 0 ≤ D) (p q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : E → ℝ) (b : NetworkVisitSpace n) (r : ℝ),
      ‖b‖ ≤ R → 0 < r → (∀ e, c e * r ≤ z e) →
      networkRoutedPolynomialCost src dst m z B b D p q ≤
        ENNReal.ofReal K * ENNReal.ofReal
          (r ^ (2 * (q + (⌈D⌉₊ + 4 * L) + 3) * Fintype.card E))⁻¹ := by
  obtain ⟨K, hK, hBound⟩ := networkRoutedTimeEnvelope G src dst hG hcover B hB R hD p q
  let p' := p + 2 * n
  let q' := q + (⌈D⌉₊ + 4 * L)
  let N := 2 * (q' + 3)
  let J (e : E) := ∫ s in Ioi (0 : ℝ), networkEdgeTimeEnvelope (m e) (p' + q' + 1) s
  have hJ (e : E) : 0 ≤ J e := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro s hs
    have hh : 0 < s := hs
    unfold networkEdgeTimeEnvelope
    positivity
  let C (e : E) := networkEdgeTimeConstant (c e) q' * J e
  have hC (e : E) : 0 ≤ C e :=
    mul_nonneg (by unfold networkEdgeTimeConstant; positivity) (hJ e)
  have hprodC : 0 ≤ ∏ e, C e := Finset.prod_nonneg (fun e _ => hC e)
  refine ⟨K * (∏ e, C e), mul_nonneg hK.le hprodC, ?_⟩
  intro z b r hb hr hz
  let μ := Measure.pi (fun _ : E => volume.restrict (Ioi (0 : ℝ)))
  let f (e : E) (s : ℝ) :=
    ENNReal.ofReal (networkTimePolynomial p' q' s * networkHeatFive (m e) (z e) s)
  have hf (e : E) : Measurable (f e) := by unfold f networkTimePolynomial networkHeatFive; fun_prop
  have hfp : Measurable (fun s : E → ℝ => ∏ e, f e (s e)) :=
    Finset.measurable_prod Finset.univ (fun e _ => (hf e).comp (measurable_pi_apply e))
  have ha : ∀ᵐ s : E → ℝ ∂μ, ∀ e, 0 < s e := by
    apply ae_all_iff.mpr
    intro e
    exact (Measure.quasiMeasurePreserving_eval _ e).ae (ae_restrict_mem measurableSet_Ioi)
  have he (e : E) : (∫⁻ s in Ioi (0 : ℝ), f e s) ≤ ENNReal.ofReal (C e / r ^ N) := by
    have h := networkEdgeTime_integral_bound (hm e) (hc e) hr (hz e) p' q'
    unfold f
    rw [← ofReal_integral_eq_lintegral_ofReal h.1 (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hh : 0 < s := hs
      exact mul_nonneg (by unfold networkTimePolynomial; positivity)
        (networkHeatFive_nonneg hh.le _ _))]
    apply ENNReal.ofReal_le_ofReal
    exact h.2.trans_eq (by unfold C N J; ring)
  calc
    _ ≤ ∫⁻ s : E → ℝ, ENNReal.ofReal K * ∏ e, f e (s e) ∂μ := by
      unfold networkRoutedPolynomialCost
      apply lintegral_mono_ae
      filter_upwards [ha] with s hs
      exact hBound m z s hs b hb
    _ = ENNReal.ofReal K * ∏ e, ∫⁻ s in Ioi (0 : ℝ), f e s := by
      calc
        _ = ENNReal.ofReal K * (∫⁻ s : E → ℝ, ∏ e, f e (s e) ∂μ) :=
          lintegral_const_mul _ hfp
        _ = _ := by rw [network_lintegral_fintype_prod _ _ hf]
    _ ≤ ENNReal.ofReal K * ∏ e, ENNReal.ofReal (C e / r ^ N) := by
      apply mul_le_mul_left'
      exact Finset.prod_le_prod' (fun e _ => he e)
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun e _ => div_nonneg (hC e) (pow_nonneg hr.le _)),
        ← ENNReal.ofReal_mul hK.le, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
        ← pow_mul, div_eq_mul_inv, ← mul_assoc, ENNReal.ofReal_mul (mul_nonneg hK.le hprodC)]

/-- One common positive boundary law suffices when it has the inverse
moment required by the fixed powers of the routed coefficient. -/
theorem networkRoutedPolynomialCost_common_law_finite {E : Type*} [Fintype E] {n L : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (m c : E → ℝ) (hm : ∀ e, 0 < m e) (hc : ∀ e, 0 < c e)
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (hB : Function.Injective B)
    (R : ℝ) {D : ℝ} (hD : 0 ≤ D) (p q : ℕ)
    (μ : Measure ℝ) (z : ℝ → E → ℝ) (b : ℝ → NetworkVisitSpace n)
    (hmark : ∀ᵐ r ∂μ, 0 < r ∧ ‖b r‖ ≤ R ∧ ∀ e, c e * r ≤ z r e)
    (hmoment : inverseMoment μ ((2 * (q + (⌈D⌉₊ + 4 * L) + 3) * Fintype.card E : ℕ) : ℝ) < ⊤) :
    (∫⁻ r, networkRoutedPolynomialCost src dst m (z r) B (b r) D p q ∂μ) < ⊤ := by
  obtain ⟨K, _, hK⟩ := networkRoutedPolynomialCost_bound G src dst hG hcover m c hm hc B hB R hD p q
  let N := 2 * (q + (⌈D⌉₊ + 4 * L) + 3) * Fintype.card E
  let f (r : ℝ) := ENNReal.ofReal ((r ^ N)⁻¹)
  have hfm : Measurable f := by unfold f; fun_prop
  have hf : (∫⁻ r, f r ∂μ) = inverseMoment μ (N : ℝ) := by
    unfold inverseMoment
    have hrpos : ∀ᵐ r ∂μ, r ∈ Ioi (0 : ℝ) := hmark.mono fun _ h => h.1
    have hrestrict : μ.restrict (Ioi (0 : ℝ)) = μ := Measure.restrict_eq_self_of_ae_mem hrpos
    rw [hrestrict]
    apply lintegral_congr_ae
    filter_upwards [hmark] with r hr
    rw [Real.rpow_neg hr.1.le, Real.rpow_natCast]
  calc
    _ ≤ ∫⁻ r, ENNReal.ofReal K * f r ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hmark] with r hr
      exact hK (z r) (b r) r hr.2.1 hr.1 hr.2.2
    _ = ENNReal.ofReal K * inverseMoment μ (N : ℝ) := by rw [lintegral_const_mul _ hfm, hf]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmoment

end UV
