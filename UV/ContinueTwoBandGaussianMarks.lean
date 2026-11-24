import UV.ContinueTwoBandSpatialWord
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Bounds for every finite directional derivative of the actual spatial
Gaussian hop. The marked polarizations are unit vectors in `Spatial`. -/

noncomputable section
open MeasureTheory Matrix Set
open scoped RealInnerProductSpace ContDiff BigOperators Matrix.Norms.L2Operator

namespace UV.SectorPlane

private def twoBandGaussianExponent (σ : ℝ) (x : Spatial) : ℝ := -(σ^2)*‖x‖^2

private theorem twoBand_gaussian_exponent_smooth (σ : ℝ) :
    ContDiff ℝ ∞ (twoBandGaussianExponent σ) := by
  unfold twoBandGaussianExponent
  exact contDiff_const.mul (contDiff_norm_sq ℝ)

private theorem twoBand_gaussian_exponent_derivative (σ : ℝ) :
    fderiv ℝ (twoBandGaussianExponent σ) = fun x => (-(2*σ^2):ℝ) • innerSL ℝ x := by
  funext x
  have hEq : twoBandGaussianExponent σ = fun x : Spatial => -(σ^2) * inner ℝ x x := by
    funext x
    rw [real_inner_self_eq_norm_sq]
    rfl
  rw [hEq]
  change fderiv ℝ (fun y => -(σ^2) * inner ℝ (id y) (id y)) x = _
  rw [(((hasFDerivAt_id x).inner ℝ (hasFDerivAt_id x)).const_mul (-(σ^2))).fderiv]
  ext u
  change -(σ^2)*(inner ℝ x u+inner ℝ u x) = -(2*σ^2)*inner ℝ x u
  rw [real_inner_comm x u]
  ring

private theorem twoBand_gaussian_exponent_derivative_norm (σ : ℝ) (j : ℕ) (hj : 1 ≤ j) (x : Spatial) :
    ‖iteratedFDeriv ℝ j (twoBandGaussianExponent σ) x‖ ≤ ((1+2*σ^2)*(1+‖x‖))^j := by
  let B : Spatial →L[ℝ] Spatial →L[ℝ] ℝ := (-(2*σ^2):ℝ) • innerSL ℝ
  have hNorm : ‖B‖ ≤ 2*σ^2 := by
    apply B.opNorm_le_bound (by positivity)
    intro y
    apply (B y).opNorm_le_bound (by positivity)
    intro z
    change ‖(-(2*σ^2):ℝ) * inner ℝ y z‖ ≤ (2*σ^2*‖y‖)*‖z‖
    have hNonneg : 0 ≤ (2*σ^2:ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hNonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (abs_real_inner_le_norm y z) hNonneg
  cases j with
  | zero => omega
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv, twoBand_gaussian_exponent_derivative]
    change ‖iteratedFDeriv ℝ j (⇑B) x‖ ≤ _
    cases j with
    | zero =>
      rw [norm_iteratedFDeriv_zero, pow_one]
      exact (B.le_opNorm x).trans ((mul_le_mul_of_nonneg_right hNorm (norm_nonneg _)).trans (by
        nlinarith [norm_nonneg x, sq_nonneg σ]))
    | succ j =>
      rw [← norm_iteratedFDeriv_fderiv]
      have hB : fderiv ℝ (⇑B) = fun _ => B := funext fun _ => B.hasFDerivAt.fderiv
      rw [hB]
      cases j with
      | zero =>
        rw [norm_iteratedFDeriv_zero]
        apply hNorm.trans
        have hBase : 1+2*σ^2 ≤ (1+2*σ^2)*(1+‖x‖) := le_mul_of_one_le_right
          (by positivity) (by linarith [norm_nonneg x])
        have hSq := pow_le_pow_left₀ (show 0 ≤ 1+2*σ^2 by positivity) hBase 2
        exact (show 2*σ^2 ≤ (1+2*σ^2)^2 by nlinarith [sq_nonneg (2*σ^2)]).trans hSq
      | succ j =>
        simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
        positivity

private theorem twoBand_gaussian_comp_smooth (σ : ℝ) : ContDiff ℝ ∞ (fun x => Real.exp (twoBandGaussianExponent σ x)) :=
  Real.contDiff_exp.comp (twoBand_gaussian_exponent_smooth σ)

theorem twoBand_gaussian_hop_smooth (g σ : ℝ) : ContDiff ℝ ∞ (twoBandSpatialHop g σ) := by
  unfold twoBandSpatialHop
  refine contDiff_const.mul ?_
  simpa only [twoBandGaussianExponent, neg_mul] using twoBand_gaussian_comp_smooth σ

theorem twoBand_gaussian_hop_derivative_norm (g σ : ℝ) (n : ℕ) (x : Spatial) :
    ‖iteratedFDeriv ℝ n (twoBandSpatialHop g σ) x‖ ≤
      |g| * (n.factorial:ℝ) * ((1+2*σ^2)*(1+‖x‖))^n * Real.exp (-(σ^2*‖x‖^2)) := by
  have hExp (j : ℕ) (_ : j ≤ n) : ‖iteratedFDeriv ℝ j Real.exp (twoBandGaussianExponent σ x)‖ ≤
      Real.exp (twoBandGaussianExponent σ x) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hb := norm_iteratedFDeriv_comp_le (N := ∞) (n := n) Real.contDiff_exp
    (twoBand_gaussian_exponent_smooth σ) (by exact_mod_cast le_top) x hExp
    (fun j hj _ => twoBand_gaussian_exponent_derivative_norm σ j hj x)
  have hEq : twoBandSpatialHop g σ = g • (Real.exp ∘ twoBandGaussianExponent σ) := by
    funext x
    simp only [twoBandSpatialHop, Pi.smul_apply, smul_eq_mul, Function.comp_apply, twoBandGaussianExponent]
    congr 2
    ring
  have hSmooth : ContDiff ℝ n (Real.exp ∘ twoBandGaussianExponent σ) :=
    (twoBand_gaussian_comp_smooth σ).of_le (by exact_mod_cast le_top)
  rw [hEq, iteratedFDeriv_const_smul_apply hSmooth.contDiffAt, norm_smul, Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left hb (abs_nonneg g)).trans_eq
  dsimp only [twoBandGaussianExponent]
  rw [neg_mul]
  ring

theorem twoBand_gaussian_mark_derivative_bound (g σ : ℝ) {n : ℕ} (u : Fin n → UnitVector Spatial) (x : Spatial) :
    ‖iteratedFDeriv ℝ n (twoBandSpatialHop g σ) x (fun j => (u j).val)‖ ≤
      |g| * (n.factorial:ℝ) * ((1+2*σ^2)*(1+‖x‖))^n * Real.exp (-(σ^2*‖x‖^2)) := by
  have h := (iteratedFDeriv ℝ n (twoBandSpatialHop g σ) x).le_opNorm (fun j => (u j).val)
  have hUnit (j : Fin n) : ‖(u j).val‖ = 1 := (u j).property
  simp only [hUnit, Finset.prod_const_one, mul_one] at h
  exact h.trans (twoBand_gaussian_hop_derivative_norm g σ n x)

theorem twoBand_gaussian_mark_envelope (g : ℝ) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Fin n → UnitVector Spatial) (x : Spatial),
      ‖iteratedFDeriv ℝ n (twoBandSpatialHop g σ) x (fun j => (u j).val)‖ ≤
        C * Real.exp (-(σ^2/2*‖x‖^2)) := by
  let a := σ^2/2
  have ha : 0 < a := by unfold a; positivity
  let K : ℝ := |g| * (n.factorial:ℝ) * (1+2*σ^2)^n
  have hK : 0 ≤ K := by unfold K; positivity
  let L : ℝ := a⁻¹^n * (n.factorial:ℝ)
  have hL : 0 ≤ L := by unfold L; positivity
  refine ⟨K * L * Real.exp (2*a), by positivity, ?_⟩
  intro u x
  let r := ‖x‖
  have hr : 0 ≤ r := norm_nonneg _
  have hSmall : 1+r ≤ 2+r^2 := by nlinarith [sq_nonneg (r-1/2)]
  have hFac : (0:ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hExp : (a*(2+r^2))^n ≤ (n.factorial:ℝ) * Real.exp (a*(2+r^2)) := by
    have h := Real.pow_div_factorial_le_exp (a*(2+r^2)) (mul_nonneg ha.le (by positivity)) n
    exact (div_le_iff₀ hFac).mp h |>.trans_eq (mul_comm _ _)
  have hBase : (1+r)^n ≤ L * Real.exp (a*(2+r^2)) := by
    calc
      _ ≤ (2+r^2)^n := pow_le_pow_left₀ (by linarith) hSmall n
      _ = a⁻¹^n * (a*(2+r^2))^n := by
        rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
      _ ≤ _ := by
        unfold L
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hExp (by positivity)
  apply (twoBand_gaussian_mark_derivative_bound g σ u x).trans
  change |g| * (n.factorial:ℝ) * ((1+2*σ^2)*(1+r))^n * Real.exp (-(σ^2*r^2)) ≤
    K * L * Real.exp (2*a) * Real.exp (-(a*r^2))
  rw [mul_pow, ← mul_assoc]
  calc
    _ = K * (1+r)^n * Real.exp (-(σ^2*r^2)) := by unfold K; ring
    _ ≤ K * (L * Real.exp (a*(2+r^2))) * Real.exp (-(σ^2*r^2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBase hK) (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc K L, mul_assoc (K*L), ← Real.exp_add, mul_assoc (K*L), ← Real.exp_add]
      congr 2
      unfold a
      ring

/-- The straight-link contact average, allowing an arbitrary probability
law of parameter shifts independent of the loop momentum. -/
def twoBandGaussianMarkAverage {S : Type*} [MeasurableSpace S] (ν : Measure S) (g σ : ℝ)
    {n : ℕ} (u : Fin n → UnitVector Spatial) (shift : S → Spatial) (k : Spatial) : ℝ :=
  ∫ s, iteratedFDeriv ℝ n (twoBandSpatialHop g σ) (k+shift s) (fun j => (u j).val) ∂ν

theorem twoBand_gaussian_mark_average {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (g : ℝ) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ (u : Fin n → UnitVector Spatial) (shift : S → Spatial),
      Measurable shift →
        Measurable (twoBandGaussianMarkAverage ν g σ u shift) ∧
        Integrable (twoBandGaussianMarkAverage ν g σ u shift) ∧
        (∀ k, ‖twoBandGaussianMarkAverage ν g σ u shift k‖ ≤ C) ∧
        (∫ k, ‖twoBandGaussianMarkAverage ν g σ u shift k‖) ≤ D := by
  obtain ⟨C,hC,hEnvelope⟩ := twoBand_gaussian_mark_envelope g hσ n
  let K := fun x : Spatial => Real.exp (-(σ^2/2*‖x‖^2))
  let D := C * ∫ x, K x
  have hK : Integrable K := by
    have h := (integrable_real_degree_gaussian (μ := (volume : Measure Spatial)) (a := σ^2/2)
      (D := 0) (by positivity) le_rfl).const_mul (1/2)
    convert h using 1
    ext x
    simp [K]
    ring
  have hD : 0 ≤ D := mul_nonneg hC (integral_nonneg (fun _ => (Real.exp_pos _).le))
  refine ⟨C,D,hC,hD,?_⟩
  intro u shift hShift
  let Φ := fun x : Spatial => iteratedFDeriv ℝ n (twoBandSpatialHop g σ) x (fun j => (u j).val)
  let f := fun p : Spatial × S => Φ (p.1+shift p.2)
  have hSmooth : ContDiff ℝ n (twoBandSpatialHop g σ) :=
    (twoBand_gaussian_hop_smooth g σ).of_le (by exact_mod_cast le_top)
  have hΦ : Continuous Φ :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Spatial) ℝ (fun j => (u j).val)).continuous.comp
      hSmooth.continuous_iteratedFDeriv'
  have hf : Measurable f := hΦ.measurable.comp (measurable_fst.add (hShift.comp measurable_snd))
  have hSection (s : S) : Integrable (fun x : Spatial => f (x,s)) ∧ (∫ x, ‖f (x,s)‖) ≤ D := by
    have hp := measurePreserving_add_right (volume : Measure Spatial) (shift s)
    let E := fun x : Spatial => C * K (x+shift s)
    have hE : Integrable E := (hp.integrable_comp_of_integrable hK).const_mul C
    have hBound (x : Spatial) : ‖f (x,s)‖ ≤ E x := hEnvelope u (x+shift s)
    have hI : Integrable (fun x : Spatial => f (x,s)) := by
      exact hE.mono' (hΦ.measurable.comp (measurable_id.add_const (shift s))).aestronglyMeasurable
        (ae_of_all _ hBound)
    refine ⟨hI, (integral_mono hI.norm hE hBound).trans_eq ?_⟩
    unfold E D
    rw [integral_const_mul]
    exact congrArg (C*·) (hp.integral_comp (Homeomorph.addRight (shift s)).measurableEmbedding K)
  have hNormI : Integrable (fun s => ∫ x, ‖f (x,s)‖) ν := by
    apply (integrable_const D).mono' (hf.aestronglyMeasurable.prod_swap.norm.integral_prod_right')
    exact ae_of_all _ (fun s => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact (hSection s).2)
  have hProd : Integrable f ((volume : Measure Spatial).prod ν) :=
    (integrable_prod_iff' hf.aestronglyMeasurable).mpr ⟨ae_of_all _ fun s => (hSection s).1,hNormI⟩
  have hFst (k : Spatial) : ‖∫ s, f (k,s) ∂ν‖ ≤ C := by
    have hPointwise : ∀ᵐ s ∂ν, ‖f (k,s)‖ ≤ C :=
      ae_of_all _ (fun s => (hEnvelope u (k+shift s)).trans
        (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))))
    simpa [Measure.real_def] using norm_integral_le_of_norm_le_const hPointwise
  refine ⟨hf.stronglyMeasurable.integral_prod_right'.measurable, hProd.integral_prod_left, hFst, ?_⟩
  change (∫ k, ‖∫ s, f (k,s) ∂ν‖) ≤ D
  calc
    _ ≤ ∫ k : Spatial, (∫ s, ‖f (k,s)‖ ∂ν) :=
      integral_mono hProd.integral_prod_left.norm hProd.norm.integral_prod_left
        (fun k => norm_integral_le_integral_norm _)
    _ = ∫ s : S, (∫ k : Spatial, ‖f (k,s)‖) ∂ν :=
      integral_integral_swap (f := fun k s => ‖f (k,s)‖) hProd.norm
    _ ≤ ∫ _ : S, D ∂ν := integral_mono hNormI (integrable_const D) (fun s => (hSection s).2)
    _ = D := by simp

def twoBandPathFractions (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => (volume : Measure ℝ).restrict (Icc 0 1))

instance (n : ℕ) : IsProbabilityMeasure (twoBandPathFractions n) := by
  letI : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Icc 0 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; norm_num⟩
  unfold twoBandPathFractions
  infer_instance

def twoBandGaussianWilsonMark (g σ : ℝ) {n : ℕ} (u : Fin n → UnitVector Spatial)
    (b : Spatial) (q : Fin n → Spatial) : Spatial → ℝ :=
  twoBandGaussianMarkAverage (twoBandPathFractions n) g σ u (fun s => b + ∑ j, s j • q j)

/-- Each label has its own straight-link parameter on `[0,1]`, with the
directional derivative evaluated at the original shifted Gaussian. -/
theorem twoBand_gaussian_wilson_marks (g : ℝ) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ (u : Fin n → UnitVector Spatial) (b : Spatial) (q : Fin n → Spatial),
      Measurable (twoBandGaussianWilsonMark g σ u b q) ∧
      Integrable (twoBandGaussianWilsonMark g σ u b q) ∧
      (∀ k, ‖twoBandGaussianWilsonMark g σ u b q k‖ ≤ C) ∧
      (∫ k, ‖twoBandGaussianWilsonMark g σ u b q k‖) ≤ D := by
  obtain ⟨C,D,hC,hD,h⟩ := twoBand_gaussian_mark_average (twoBandPathFractions n) g hσ n
  refine ⟨C,D,hC,hD,?_⟩
  intro u b q
  refine h u (fun s => b + ∑ j, s j • q j) ?_
  apply Measurable.const_add
  exact Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).smul measurable_const)

theorem twoBand_wilson_multipliers_integrable {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : ℝ) {σ : ℝ} (hσ : 0 < σ) (n : ι → ℕ) (u : ∀ i, Fin (n i) → UnitVector Spatial)
    (b : ι → Spatial) (q : ∀ i, Fin (n i) → Spatial) :
    Integrable (fun k => ∏ i, twoBandGaussianWilsonMark g σ (u i) (b i) (q i) k) := by
  classical
  let W := fun i => twoBandGaussianWilsonMark g σ (u i) (b i) (q i)
  have h (i : ι) : ∃ C_i : ℝ, Measurable (W i) ∧ Integrable (W i) ∧ ∀ k, ‖W i k‖ ≤ C_i := by
    obtain ⟨C,D,_,_,hBound⟩ := twoBand_gaussian_wilson_marks g hσ (n i)
    exact ⟨C,(hBound (u i) (b i) (q i)).1,(hBound (u i) (b i) (q i)).2.1,
      (hBound (u i) (b i) (q i)).2.2.1⟩
  choose C hMeas hI hBound using h
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  let S := Finset.univ.erase i₀
  let T := fun k => ∏ i ∈ S, W i k
  have hT : Measurable T := Finset.measurable_prod _ (fun i _ => hMeas i)
  have hNorm (k : Spatial) : ‖T k‖ ≤ ∏ i ∈ S, C i := by
    rw [show ‖T k‖ = ∏ i ∈ S, ‖W i k‖ by exact norm_prod _ _]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hBound i k)
  have hTW := (hI i₀).bdd_mul' hT.aestronglyMeasurable (ae_of_all _ hNorm)
  apply hTW.congr
  exact ae_of_all _ (fun k => Finset.prod_erase_mul Finset.univ (fun i => W i k) (Finset.mem_univ i₀))

theorem twoBand_wilson_contact_integrable {m σ : ℝ} (hm : 0 < m) (hσ : 0 < σ)
    (g ξ₀ : ℝ) (c : Spatial) {n : ℕ} (u : Fin n → UnitVector Spatial) (b : Spatial) (q : Fin n → Spatial) :
    Integrable (fun p : ℝ × Spatial => (twoBandGaussianWilsonMark g σ u b q p.2 : ℂ) *
      (twoBandResolvent m (twoBandSpatialHop g σ (p.2+c)) (p.1+ξ₀) * twoBandMix).trace) := by
  obtain ⟨C,_,_,_,h⟩ := twoBand_gaussian_wilson_marks g hσ n
  have hs := h u b q
  have hn (k : Spatial) : ‖(twoBandGaussianWilsonMark g σ u b q k : ℂ)‖ ≤ C := by
    rw [Complex.norm_real]
    exact hs.2.2.1 k
  exact twoBand_single_spatial_contact_integrable hm hσ g ξ₀ c _ (Complex.continuous_ofReal.measurable.comp hs.1) hn

theorem twoBand_wilson_spatial_word_integrable {ι : Type*} [Fintype ι] [Nonempty ι] {m σ : ℝ}
    (hm : 0 < m) (hσ : 0 < σ) (g : ℝ) (r : ℕ) (ξ₀ : ℕ → ℝ) (c : ℕ → Spatial) (mark : ℕ → Bool)
    (n : ι → ℕ) (u : ∀ i, Fin (n i) → UnitVector Spatial) (b : ι → Spatial) (q : ∀ i, Fin (n i) → Spatial) :
    Integrable (fun p : ℝ × Spatial => ((∏ i, twoBandGaussianWilsonMark g σ (u i) (b i) (q i) p.2 : ℝ) : ℂ) *
      (twoBandOrderedProduct (fun j => twoBandResolvent m (twoBandSpatialHop g σ (p.2+c j))
        (p.1+ξ₀ j) * (if mark j then twoBandMix else 1)) (r+2)).trace) := by
  let M := fun j : ℕ => if mark j then twoBandMix else 1
  have hM (j : ℕ) : ‖M j‖ ≤ 1 := by cases h : mark j <;> simp [M, h, twoBand_mix_norm]
  have hW := twoBand_wilson_multipliers_integrable g hσ n u b q
  exact twoBand_spatial_word_integrable hm g σ ξ₀ c M hM _ (Complex.ofRealCLM.integrable_comp hW) r

end UV.SectorPlane
