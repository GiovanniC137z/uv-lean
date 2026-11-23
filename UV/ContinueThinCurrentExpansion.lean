import UV.ContinueThinCurrentKernel
import UV.ContinueThinCurrentSpectral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact shell expansion with the physical Fourier normalization,
including all signed edge pairs. -/

set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ENNReal BigOperators ComplexConjugate

namespace UV

def thinWindowInverse (φ : ThinCurrentPlane → ℝ) (x : ThinCurrentPlane) : ℂ :=
  (((2 * Real.pi) ^ 4)⁻¹ : ℝ) • ∫ p, (φ p : ℂ) * thinPlaneWave p x

def thinEdgePairWeight (e e' : ThinCurrentSegment) : ℝ :=
  (e.multiplicity : ℝ) * (e'.multiplicity : ℝ) * inner ℝ e.tangent e'.tangent

theorem thinEdgePairWeight_self (e : ThinCurrentSegment) :
    thinEdgePairWeight e e = (e.multiplicity : ℝ) ^ 2 := by
  simp [thinEdgePairWeight, real_inner_self_eq_norm_sq, e.unit_tangent, pow_two]

private theorem thinPlaneWave_norm (p x : ThinCurrentPlane) : ‖thinPlaneWave p x‖ = 1 := by
  simp [thinPlaneWave, Complex.norm_exp, Complex.mul_re]

private theorem thinPlaneWave_sub (p x y : ThinCurrentPlane) :
    thinPlaneWave p (x - y) = thinPlaneWave p x * conj (thinPlaneWave p y) := by
  unfold thinPlaneWave
  rw [← Complex.exp_conj, ← Complex.exp_add, inner_sub_right]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

private theorem thinSegment_set_integral (e : ThinCurrentSegment) (p : ThinCurrentPlane) :
    thinCurrentSegmentWave e p = ∫ s in Ioo 0 e.length, thinPlaneWave p (e.point s) := by
  unfold thinCurrentSegmentWave
  rw [intervalIntegral.integral_of_le e.length_nonneg, integral_Ioc_eq_integral_Ioo]

theorem thinSegmentWave_norm_le (e : ThinCurrentSegment) (p : ThinCurrentPlane) :
    ‖thinCurrentSegmentWave e p‖ ≤ e.length := by
  rw [thinSegment_set_integral]
  haveI : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo 0 e.length)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  have h := norm_integral_le_of_norm_le (μ := (volume : Measure ℝ).restrict (Ioo 0 e.length))
    (g := fun _ => (1 : ℝ)) (integrable_const _) (Eventually.of_forall fun s =>
      (thinPlaneWave_norm p (e.point s)).le)
  rw [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
    ENNReal.toReal_ofReal e.length_nonneg, smul_eq_mul, mul_one] at h
  exact h

private theorem thinSegmentWave_measurable (e : ThinCurrentSegment) :
    Measurable (thinCurrentSegmentWave e) := by
  have h : Continuous (fun ps : ThinCurrentPlane × ℝ => thinPlaneWave ps.1 (e.point ps.2)) := by
    unfold thinPlaneWave ThinCurrentSegment.point
    fun_prop
  change Measurable (fun p => thinCurrentSegmentWave e p)
  simp_rw [thinSegment_set_integral]
  exact (h.measurable.stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Ioo 0 e.length))).measurable

private theorem thinSegmentPair_expand (e e' : ThinCurrentSegment) (p : ThinCurrentPlane) :
    thinCurrentSegmentWave e p * conj (thinCurrentSegmentWave e' p) =
      ∫ u in Ioo 0 e'.length, ∫ s in Ioo 0 e.length,
        thinPlaneWave p (e.point s - e'.point u) := by
  rw [thinSegment_set_integral, thinSegment_set_integral, ← integral_conj, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with s
  exact (thinPlaneWave_sub p _ _).symm

private theorem thinCurrentNormSq_expand {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment) (p : ThinCurrentPlane) :
    ((thinCurrentNormSq edges p : ℝ) : ℂ) =
      ∑ j, ∑ k, (thinEdgePairWeight (edges j) (edges k) : ℂ) *
        (thinCurrentSegmentWave (edges j) p * conj (thinCurrentSegmentWave (edges k) p)) := by
  unfold thinCurrentNormSq thinCurrent thinEdgePairWeight
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul, map_intCast, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

private theorem thinWindowInverse_scaled (φ : ThinCurrentPlane → ℝ) {R : ℝ} (hR : 0 < R)
    (x : ThinCurrentPlane) :
    ((((2 * Real.pi) ^ 4)⁻¹ : ℝ) • ∫ p, (φ (R⁻¹ • p) : ℂ) * thinPlaneWave p x) =
      R ^ 4 • thinWindowInverse φ (R • x) := by
  have hphase (p : ThinCurrentPlane) : thinPlaneWave p x = thinPlaneWave (R⁻¹ • p) (R • x) := by
    unfold thinPlaneWave
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
  have hdim : Module.finrank ℝ ThinCurrentPlane = 4 := by simp [ThinCurrentPlane]
  simp_rw [hphase]
  have hs := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ThinCurrentPlane)
    (fun p => (φ p : ℂ) * thinPlaneWave p (R • x)) hR.le
  rw [hdim] at hs
  rw [hs, thinWindowInverse, smul_comm]

private theorem thinEdgePair_window {φ : ThinCurrentPlane → ℝ} (hφ : Continuous φ)
    {R : ℝ} (hR : 0 < R) (hI : Integrable (fun p => φ (R⁻¹ • p)))
    (e e' : ThinCurrentSegment) :
    ((((2 * Real.pi) ^ 4)⁻¹ : ℝ) • ∫ p, (φ (R⁻¹ • p) : ℂ) *
      (thinCurrentSegmentWave e p * conj (thinCurrentSegmentWave e' p))) =
      R ^ 3 • thinEdgeNormalizedPair (thinWindowInverse φ) e e' R := by
  let μ : Measure ℝ := volume.restrict (Ioo 0 e.length)
  let ν : Measure ℝ := volume.restrict (Ioo 0 e'.length)
  let F (p : ThinCurrentPlane) (q : ℝ × ℝ) :=
    (φ (R⁻¹ • p) : ℂ) * thinPlaneWave p (e.point q.2 - e'.point q.1)
  haveI : IsFiniteMeasure μ :=
    ⟨by dsimp [μ]; rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure ν :=
    ⟨by dsimp [ν]; rw [Measure.restrict_apply_univ, Real.volume_Ioo]; exact ENNReal.ofReal_lt_top⟩
  have hcont : Continuous (Function.uncurry F) := by
    unfold Function.uncurry F thinPlaneWave ThinCurrentSegment.point
    fun_prop
  have hFi : Integrable (Function.uncurry F) (volume.prod (ν.prod μ)) := by
    refine (hI.norm.comp_fst (ν.prod μ)).mono' hcont.aestronglyMeasurable ?_
    exact Eventually.of_forall fun z => by simp [F, Function.uncurry, thinPlaneWave_norm]
  have hFq (p : ThinCurrentPlane) : Integrable (F p) (ν.prod μ) := by
    have hm : Continuous (F p) := by
      unfold F thinPlaneWave ThinCurrentSegment.point
      fun_prop
    exact (integrable_const ‖φ (R⁻¹ • p)‖).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun q => by simp [F, thinPlaneWave_norm])
  have hswap := integral_integral_swap hFi
  let c := (((2 * Real.pi) ^ 4)⁻¹ : ℝ)
  calc
    _ = c • ∫ p, ∫ q, F p q ∂(ν.prod μ) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with p
      rw [integral_prod _ (hFq p), thinSegmentPair_expand]
      simp only [F, integral_const_mul]
      rfl
    _ = c • ∫ q, (∫ p, F p q) ∂(ν.prod μ) := congrArg (c • ·) hswap
    _ = R ^ 4 • ∫ u, (∫ s, thinWindowInverse φ (R • (e.point s - e'.point u)) ∂μ) ∂ν := by
      rw [← integral_smul]
      have heq :
          (fun q => c • ∫ p, F p q) =
            fun q => R ^ 4 • thinWindowInverse φ (R • (e.point q.2 - e'.point q.1)) := by
        funext q
        exact thinWindowInverse_scaled φ hR _
      rw [heq, integral_smul]
      rw [integral_prod]
      have hcI := (hFi.swap.integral_prod_left.smul c).smul ((R ^ 4)⁻¹)
      apply hcI.congr
      apply Eventually.of_forall
      intro q
      change ((R ^ 4)⁻¹ : ℝ) • (c • ∫ p, F p q) =
        thinWindowInverse φ (R • (e.point q.2 - e'.point q.1))
      rw [congrFun heq q, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hR.ne'), one_smul]
    _ = _ := by
      rw [thinEdgeNormalizedPair_eq _ e e' hR, smul_smul]
      rw [pow_succ]

/-- Exact identification of the positive shell with its rescaled
arclength-pair Fourier expansion, with no change of the tangent vectors. -/
theorem thinCurrentShell_eq_pair_sum {ι : Type*} [Fintype ι] {φ : ThinCurrentPlane → ℝ}
    (hφ : Continuous φ) (hφI : Integrable φ) (hpos : ∀ p, 0 ≤ φ p)
    (edges : ι → ThinCurrentSegment) {R : ℝ} (hR : 0 < R) :
    (thinCurrentShell edges φ R).toReal / R ^ 3 =
      (∑ j, ∑ k, (thinEdgePairWeight (edges j) (edges k) : ℂ) *
        thinEdgeNormalizedPair (thinWindowInverse φ) (edges j) (edges k) R).re := by
  classical
  have hI : Integrable (fun p => φ (R⁻¹ • p)) :=
    (integrable_comp_smul_iff volume φ (inv_ne_zero hR.ne')).mpr hφI
  have hpair (e e' : ThinCurrentSegment) :
      Integrable (fun p => (φ (R⁻¹ • p) : ℂ) *
        (thinCurrentSegmentWave e p * conj (thinCurrentSegmentWave e' p))) := by
    refine (hI.norm.const_mul (e.length * e'.length)).mono' ?_ ?_
    · exact ((Complex.continuous_ofReal.measurable.comp ((hφ.comp (continuous_const.smul
        continuous_id)).measurable)).mul ((thinSegmentWave_measurable e).mul
          (Complex.continuous_conj.measurable.comp (thinSegmentWave_measurable e')))).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      simp only [norm_mul, Complex.norm_real, Complex.norm_conj]
      rw [mul_comm (e.length * e'.length)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (thinSegmentWave_norm_le e p) (thinSegmentWave_norm_le e' p)
          (norm_nonneg _) e.length_nonneg) (norm_nonneg _)
  have hInt : Integrable (fun p => (φ (R⁻¹ • p) : ℂ) * (thinCurrentNormSq edges p : ℂ)) := by
    simp_rw [thinCurrentNormSq_expand, Finset.mul_sum]
    exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
      ((hpair (edges j) (edges k)).const_mul (thinEdgePairWeight (edges j) (edges k) : ℂ)).congr
        (Eventually.of_forall fun p => by ring)
  have hReal : Integrable (fun p => φ (R⁻¹ • p) * thinCurrentNormSq edges p) := by
    apply Integrable.re (𝕜 := ℂ) at hInt
    simpa only [← Complex.ofReal_mul, Complex.ofReal_re] using hInt
  let c : ℝ := ((2 * Real.pi) ^ 4)⁻¹
  have hc : 0 ≤ c := by positivity
  have hN (p : ThinCurrentPlane) : 0 ≤ φ (R⁻¹ • p) * thinCurrentNormSq edges p :=
    mul_nonneg (hpos _) (thinCurrentNormSq_nonneg _ _)
  have hmass :
      (thinCurrentShell edges φ R).toReal =
        (c • ∫ p, (φ (R⁻¹ • p) : ℂ) * (thinCurrentNormSq edges p : ℂ)).re := by
    unfold thinCurrentShell thinCurrentMomentumMeasure
    rw [lintegral_smul_measure, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc,
      ← ofReal_integral_eq_lintegral_ofReal hReal (Eventually.of_forall hN),
      ENNReal.toReal_ofReal (integral_nonneg hN)]
    simp_rw [← Complex.ofReal_mul]
    rw [integral_complex_ofReal]
    simp
  rw [hmass]
  have hsum :
      (c • ∫ p, (φ (R⁻¹ • p) : ℂ) * (thinCurrentNormSq edges p : ℂ)) =
        R ^ 3 • ∑ j, ∑ k, (thinEdgePairWeight (edges j) (edges k) : ℂ) *
          thinEdgeNormalizedPair (thinWindowInverse φ) (edges j) (edges k) R := by
    simp_rw [thinCurrentNormSq_expand, Finset.mul_sum]
    rw [integral_finset_sum]
    · simp only [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finset_sum]
      · simp only [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro k _
        have heq (p : ThinCurrentPlane) :
            (φ (R⁻¹ • p) : ℂ) * ((thinEdgePairWeight (edges j) (edges k) : ℂ) *
              (thinCurrentSegmentWave (edges j) p * conj (thinCurrentSegmentWave (edges k) p))) =
            (thinEdgePairWeight (edges j) (edges k) : ℂ) *
              ((φ (R⁻¹ • p) : ℂ) *
                (thinCurrentSegmentWave (edges j) p * conj (thinCurrentSegmentWave (edges k) p))) := by ring
        simp_rw [heq]
        rw [integral_const_mul]
        let q : ℂ := (thinEdgePairWeight (edges j) (edges k) : ℂ)
        let I : ℂ := ∫ p, (φ (R⁻¹ • p) : ℂ) *
          (thinCurrentSegmentWave (edges j) p * conj (thinCurrentSegmentWave (edges k) p))
        let J := thinEdgeNormalizedPair (thinWindowInverse φ) (edges j) (edges k) R
        change c • (q * I) = R ^ 3 • (q * J)
        calc
          _ = q * (c • I) := by simp only [Complex.real_smul]; ring
          _ = q * (R ^ 3 • J) := congrArg (q * ·) (thinEdgePair_window hφ hR hI _ _)
          _ = _ := by simp only [Complex.real_smul]; ring
      · intro k _
        exact ((hpair (edges j) (edges k)).const_mul _).congr (Eventually.of_forall fun p => by ring)
    · intro j _
      exact integrable_finset_sum _ fun k _ =>
        ((hpair (edges j) (edges k)).const_mul _).congr (Eventually.of_forall fun p => by ring)
  rw [hsum, Complex.smul_re, smul_eq_mul, mul_comm, mul_div_cancel_right₀ _ (pow_ne_zero _ hR.ne')]

end UV
