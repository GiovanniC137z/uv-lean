import UV.VerifyNetworkMarkedBounds
import UV.AdvanceNetworkJoint

/-! Joint momentum and proper-time costs for actual shared-vertex
displacement products, with the original normalized loop measure. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace UV

def networkMarkedPolynomialCost {E : Type*} [Fintype E] {n L : ℕ}
    (src dst : E → Option (Fin n)) (m z : E → ℝ)
    (directions : List (NetworkVisitSpace n))
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (b : NetworkVisitSpace n)
    (D : ℝ) (p q : ℕ) : ℝ≥0∞ :=
  ∫⁻ s : E → ℝ, ∫⁻ k : NetworkVisitSpace L, ENNReal.ofReal
    ((∏ e, networkTimePolynomial p q (s e)) * ((1 / (2 * Real.pi) ^ (4 * L)) *
      ((1 + ‖k‖ ^ D) * ‖networkMarkedFourier src dst m z s directions (B k + b)‖)))
    ∂volume ∂Measure.pi (fun _ : E => volume.restrict (Ioi (0 : ℝ)))

private theorem networkDurationBox_single {E : Type*} [Fintype E]
    (f : E → ℝ) (hf : ∀ e, 1 ≤ f e) (e : E) : f e ≤ ∏ i, f i := by
  classical
  have h : 1 ≤ ∏ i ∈ (Finset.univ : Finset E).erase e, f i := by
    simpa only [Finset.prod_const_one] using
      Finset.prod_le_prod (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) (fun i _ => hf i)
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ e)]
  exact le_mul_of_one_le_right (zero_le_one.trans (hf e)) h

private theorem networkDurationBox_positive {E : Type*} [Fintype E]
    (s : E → ℝ) (hs : ∀ e, 0 < s e) :
    let T := ∏ e : E, (1 + s e)
    1 ≤ T ∧ ∃ smin : ℝ, 0 < smin ∧ ∀ e, smin ≤ s e ∧ s e ≤ T := by
  let V := ∏ e : E, (1 + (s e)⁻¹)
  have hT : 1 ≤ ∏ e : E, (1 + s e) := by
    simpa only [Finset.prod_const_one] using
      Finset.prod_le_prod (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1))
        (fun e _ => le_add_of_nonneg_right (hs e).le)
  have hV : 1 ≤ V := by
    simpa only [Finset.prod_const_one] using
      Finset.prod_le_prod (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1))
        (fun e _ => le_add_of_nonneg_right (inv_nonneg.mpr (hs e).le))
  refine ⟨hT, V⁻¹, inv_pos.mpr (zero_lt_one.trans_le hV), ?_⟩
  intro e
  have hv := networkDurationBox_single (fun i => 1 + (s i)⁻¹)
    (fun i => le_add_of_nonneg_right (inv_nonneg.mpr (hs i).le)) e
  have ht := networkDurationBox_single (fun i => 1 + s i)
    (fun i => le_add_of_nonneg_right (hs i).le) e
  have h := (le_add_of_nonneg_left zero_le_one : (s e)⁻¹ ≤ 1 + (s e)⁻¹).trans hv
  exact ⟨by simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (hs e)) h,
    (le_add_of_nonneg_left zero_le_one).trans ht⟩

private theorem networkMomentum_combined_degree {x D : ℝ} (hx : 0 ≤ x)
    (hD : 0 ≤ D) (r : ℕ) :
    (1 + x ^ D) * (1 + x) ^ r ≤ (2 : ℝ) ^ (r + 1) * (1 + x ^ (⌈D⌉₊ + r)) := by
  by_cases hsmall : x ≤ 1
  · have hR : (1 + x) ^ r ≤ (2 : ℝ) ^ r :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hD1 : 1 + x ^ D ≤ 2 := by linarith [Real.rpow_le_one hx hsmall hD]
    calc
      _ ≤ 2 * (2 : ℝ) ^ r := mul_le_mul hD1 hR (by positivity) (by norm_num)
      _ = (2 : ℝ) ^ (r + 1) := by rw [pow_succ]; ring
      _ ≤ _ := by
        exact le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_right (pow_nonneg hx _))
  · have hx1 : 1 ≤ x := le_of_not_ge hsmall
    have hDpow : x ^ D ≤ x ^ ⌈D⌉₊ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hx1 (Nat.le_ceil D)
    have hD1 : 1 + x ^ D ≤ 2 * x ^ ⌈D⌉₊ := by
      linarith only [hDpow, one_le_pow₀ hx1 (n := ⌈D⌉₊)]
    have hR : (1 + x) ^ r ≤ (2 * x) ^ r :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      _ ≤ (2 * x ^ ⌈D⌉₊) * (2 * x) ^ r := mul_le_mul hD1 hR (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (r + 1) * x ^ (⌈D⌉₊ + r) := by rw [mul_pow, pow_succ, pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)

private theorem networkTimePolynomial_prod_shift {E : Type*} [Fintype E]
    (s : E → ℝ) (p q d : ℕ) :
    (∏ e, networkTimePolynomial p q (s e)) * (∏ e : E, (1 + s e)) ^ d =
      ∏ e, networkTimePolynomial (p + d) q (s e) := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  unfold networkTimePolynomial
  rw [pow_add]
  ring

/-- The normalized absolute marked cost is dominated by the existing
unmarked routed cost after raising the time and momentum degrees. -/
theorem networkMarkedPolynomialCost_le_routed {E : Type*} [Fintype E] {n L : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (directions : List (NetworkVisitSpace n))
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (R : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m z : E → ℝ) (b : NetworkVisitSpace n), ‖b‖ ≤ R →
      ∀ p q : ℕ,
        networkMarkedPolynomialCost src dst m z directions B b D p q ≤
          ENNReal.ofReal K * networkRoutedPolynomialCost src dst m z B b
            ((⌈D⌉₊ + directions.length : ℕ) : ℝ) (p + directions.length) q := by
  obtain ⟨C, hC, hBound⟩ :=
    networkMarkedFourier_norm_bound G src dst hG hcover directions
  let d := directions.length
  let c := 1 + ‖B‖ + |R|
  let K := C * (2 : ℝ) ^ d * c ^ d * (2 : ℝ) ^ (d + 1)
  have hc : 0 ≤ c := by unfold c; positivity
  have hK : 0 ≤ K := by unfold K; positivity
  refine ⟨K, hK, ?_⟩
  intro m z b hb p q
  let ν := Measure.pi (fun _ : E => volume.restrict (Ioi (0 : ℝ)))
  let S := ENNReal.ofReal K
  let f (s : E → ℝ) (k : NetworkVisitSpace L) :=
    (∏ e, networkTimePolynomial (p + d) q (s e)) * ((1 / (2 * Real.pi) ^ (4 * L)) *
      ((1 + ‖k‖ ^ ((⌈D⌉₊ + d : ℕ) : ℝ)) * ‖networkRoutedFourier src dst m z s B b k‖))
  have hRight : S * networkRoutedPolynomialCost src dst m z B b
        ((⌈D⌉₊ + d : ℕ) : ℝ) (p + d) q =
      ∫⁻ s, ∫⁻ k, S * ENNReal.ofReal (f s k) ∂volume ∂ν := by
    simp only [networkRoutedPolynomialCost, f, ν]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro s
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  change networkMarkedPolynomialCost src dst m z directions B b D p q ≤
    S * networkRoutedPolynomialCost src dst m z B b
      ((⌈D⌉₊ + d : ℕ) : ℝ) (p + d) q
  rw [hRight]
  unfold networkMarkedPolynomialCost
  apply lintegral_mono_ae
  have ha : ∀ᵐ s : E → ℝ ∂ν, ∀ e, 0 < s e := by
    apply ae_all_iff.mpr
    intro e
    exact (Measure.quasiMeasurePreserving_eval _ e).ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [ha] with s hs
  apply lintegral_mono
  intro k
  let T := ∏ e : E, (1 + s e)
  obtain ⟨hT, t, ht, hbox⟩ := networkDurationBox_positive s hs
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hTime := networkTimePolynomial_prod_shift s p q d
  have hMark := hBound m z s t T ht hT0 hbox (B k + b)
  have hB : 1 + ‖B k + b‖ ≤ c * (1 + ‖k‖) := by
    have hB1 := (norm_add_le (B k) b).trans (add_le_add (B.le_opNorm k) (hb.trans (le_abs_self R)))
    have hsM := mul_nonneg (abs_nonneg R) (norm_nonneg k)
    dsimp [c]
    nlinarith only [hB1, hsM, norm_nonneg B, norm_nonneg k, abs_nonneg R]
  have hma := mul_le_mul (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + T)
      (by linarith only [hT] : 1 + T ≤ 2 * T) d)
    (pow_le_pow_left₀ (by positivity) hB d) (by positivity) (by positivity)
  have hmark2 :
      ‖networkMarkedFourier src dst m z s directions (B k + b)‖ ≤
        ((C * (2 : ℝ) ^ d * c ^ d) * T ^ d * (1 + ‖k‖) ^ d) *
          ‖networkRoutedFourier src dst m z s B b k‖ := by
    refine hMark.trans ?_
    change (C * (1 + T) ^ d * (1 + ‖B k + b‖) ^ d) *
      ‖networkRoutedFourier src dst m z s B b k‖ ≤ _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ = C * ((1 + T) ^ d * (1 + ‖B k + b‖) ^ d) := by ring
      _ ≤ C * ((2 * T) ^ d * (c * (1 + ‖k‖)) ^ d) := mul_le_mul_of_nonneg_left hma hC
      _ = _ := by rw [mul_pow, mul_pow]; ring
  have hMom := networkMomentum_combined_degree (norm_nonneg k) hD d
  let M := ∏ e, networkTimePolynomial p q (s e)
  let A : ℝ := 1 / (2 * Real.pi) ^ (4 * L)
  have hM : 0 ≤ M := Finset.prod_nonneg fun e _ => by
    have hs' := hs e
    unfold networkTimePolynomial
    positivity
  have hA : 0 ≤ A := by unfold A; positivity
  change ENNReal.ofReal (M * (A * ((1 + ‖k‖ ^ D) *
    ‖networkMarkedFourier src dst m z s directions (B k + b)‖))) ≤
      ENNReal.ofReal K * ENNReal.ofReal (f s k)
  rw [← ENNReal.ofReal_mul hK]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ M * (A * ((1 + ‖k‖ ^ D) *
          (((C * (2 : ℝ) ^ d * c ^ d) * T ^ d * (1 + ‖k‖) ^ d) *
            ‖networkRoutedFourier src dst m z s B b k‖))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmark2 (by positivity)) hA) hM
    _ = (C * (2 : ℝ) ^ d * c ^ d) * (M * T ^ d) * A *
          ‖networkRoutedFourier src dst m z s B b k‖ * ((1 + ‖k‖ ^ D) * (1 + ‖k‖) ^ d) := by ring
    _ ≤ (C * (2 : ℝ) ^ d * c ^ d) * (M * T ^ d) * A *
          ‖networkRoutedFourier src dst m z s B b k‖ *
            ((2 : ℝ) ^ (d + 1) * (1 + ‖k‖ ^ (⌈D⌉₊ + d))) :=
      mul_le_mul_of_nonneg_left hMom (by positivity)
    _ = K * f s k := by
      have hTM : M * T ^ d = ∏ e, networkTimePolynomial (p + d) q (s e) := hTime
      rw [hTM]
      unfold K f A
      rw [Real.rpow_natCast]
      ring

/-- The actual displacement-marked graph cost obeys a finite power
bound uniform in the jointly varying positive transverse marks. -/
theorem networkMarkedPolynomialCost_bound {E : Type*} [Fintype E] {n L : ℕ}
    (G : SimpleGraph (Option (Fin n))) (src dst : E → Option (Fin n))
    (hG : G.Connected) (hcover : NetworkOrientationCovers G src dst)
    (m c : E → ℝ) (hm : ∀ e, 0 < m e) (hc : ∀ e, 0 < c e)
    (directions : List (NetworkVisitSpace n))
    (B : NetworkVisitSpace L →L[ℝ] NetworkVisitSpace n) (hB : Function.Injective B)
    (R : ℝ) {D : ℝ} (hD : 0 ≤ D) (p q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : E → ℝ) (b : NetworkVisitSpace n) (r : ℝ),
      ‖b‖ ≤ R → 0 < r → (∀ e, c e * r ≤ z e) →
      networkMarkedPolynomialCost src dst m z directions B b D p q ≤
        ENNReal.ofReal K * ENNReal.ofReal
          (r ^ (2 * (q + (⌈D⌉₊ + directions.length + 4 * L) + 3) * Fintype.card E))⁻¹ := by
  let a := ⌈D⌉₊ + directions.length
  obtain ⟨C, hC, hmark⟩ :=
    networkMarkedPolynomialCost_le_routed G src dst hG hcover directions B R hD
  obtain ⟨K, hK, hbound⟩ := networkRoutedPolynomialCost_bound G src dst hG hcover m c hm hc B hB
    R (by positivity : 0 ≤ (a : ℝ)) (p + directions.length) q
  refine ⟨C * K, mul_nonneg hC hK, ?_⟩
  intro z b r hb hr hz
  have h := (hmark m z b hb p q).trans (mul_le_mul_left' (hbound z b r hb hr hz) _)
  simpa only [a, Nat.ceil_natCast, ENNReal.ofReal_mul hC, mul_assoc] using h

end UV
