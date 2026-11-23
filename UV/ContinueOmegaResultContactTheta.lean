import UV.ContinueOmegaResultFourierContact
import UV.ContinueNormalHolonomyTheta

/-! Four-dimensional Gaussian lattice sum for a transversely projected
positive Laplace covariance. The isolated zero momentum is removed
explicitly; the zero heat width is kept as a possible atom. -/

noncomputable section
open MeasureTheory Set Filter UV.ContinueNormalHolonomy
open scoped Topology ENNReal NNReal Matrix ComplexOrder MatrixOrder

namespace UV

private theorem contact_int_gaussian {t : ℝ} (ht : 0 < t) : Summable (fun k : ℤ => Real.exp (-t*(k:ℝ)^2)) := by
  have h : Summable (fun n : ℕ => Real.exp (-t*(n:ℝ)^2)) := by
    have he := summable_geometric_of_lt_one (Real.exp_pos (-t)).le (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht))
    apply Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) _ he
    intro n
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hn : (n:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast (Nat.le_self_pow (by decide) n)
    nlinarith [mul_le_mul_of_nonneg_left hn ht.le]
  simpa [summable_int_iff_summable_nat_and_neg] using And.intro h h

private theorem contact_theta_one {t : ℝ} (ht : 0 < t) :
    1 ≤ normalTheta t 0 := by
  have h := (contact_int_gaussian ht).sum_le_tsum ({0} : Finset ℤ) (fun _ _ => (Real.exp_pos _).le)
  simpa [normalTheta] using h

private theorem contact_theta_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : normalTheta t 0 ≤ normalTheta s 0 := by
  simp only [normalTheta,sub_zero]
  exact (contact_int_gaussian (hs.trans_le hst)).tsum_le_tsum
    (fun n => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hst) (sq_nonneg _))) (contact_int_gaussian hs)

theorem contact_theta_small {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) :
    Real.sqrt (Real.pi/t) ≤ normalTheta t 0 ∧
    normalTheta t 0 ≤ Real.sqrt (Real.pi/t)*normalTheta 1 0 := by
  have hv : 0 < Real.pi^2/t := by positivity
  have he := normalTheta_poisson ht 0
  have hθ : normalTheta t 0 = Real.sqrt (Real.pi/t)*normalTheta (Real.pi^2/t) 0 := by
    simpa [normalTheta,neg_div] using he
  rw [hθ]
  constructor
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left (contact_theta_one hv) (Real.sqrt_nonneg _)
  · apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply contact_theta_mono zero_lt_one
    rw [le_div_iff₀ ht]
    nlinarith [Real.pi_gt_three]

private theorem contact_count_pi {d : ℕ} :
    Measure.pi (fun _ : Fin d => (Measure.count : Measure ℤ)) = (Measure.count : Measure (Fin d → ℤ)) := by
  apply Measure.ext_of_singleton
  intro p
  rw [←Set.univ_pi_singleton p,Measure.pi_pi,Set.univ_pi_singleton]
  simp

/-- Fubini gives the exact fourth power of the one-dimensional theta
series, with Lebesgue counting measure on all four lattice coordinates. -/
theorem contact_gaussian_sum {t : ℝ} (ht : 0 < t) :
    let F := fun p : Fin 4 → ℤ => Real.exp (-t*(∑ i, (p i:ℝ)^2))
    Summable F ∧ (∑' p, F p) = normalTheta t 0 ^ 4 := by
  let a := fun k : ℤ => Real.exp (-t*(k:ℝ)^2)
  have ha : Integrable a Measure.count := integrable_count_iff.mpr (by
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),a] using contact_int_gaussian ht)
  have he (p : Fin 4 → ℤ) : Real.exp (-t*(∑ i, (p i : ℝ)^2)) = ∏ i, a (p i) := by
    rw [Finset.mul_sum,Real.exp_sum]
  have hP := Integrable.fintype_prod (ι := Fin 4) (fun _ => ha)
  rw [contact_count_pi] at hP
  have hh : Integrable (fun p : Fin 4 → ℤ => Real.exp (-t*(∑ i, (p i:ℝ)^2))) Measure.count := by
    simpa only [he] using hP
  have hsum := integrable_count_iff.mp hh
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hsum
  refine ⟨hsum,?_⟩
  calc
    _ = ∫ p : Fin 4 → ℤ, Real.exp (-t*(∑ i, (p i:ℝ)^2)) ∂Measure.count := by
      rw [integral_countable' hh]
      simp
    _ = ∫ p, ∏ i, a (p i) ∂Measure.pi (fun _ : Fin 4 => (Measure.count : Measure ℤ)) := by
      simp_rw [he,contact_count_pi]
    _ = _ := by
      rw [integral_fintype_prod_eq_prod (fun _ : Fin 4 => a),integral_countable' ha]
      simp [normalTheta,a]

def contactHeatTrace (t : ℝ) : ℝ := ∑' p : CurvatureMode, Real.exp (-t*contactModeSquare p)

private theorem contact_heat_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun p : CurvatureMode => Real.exp (-t*contactModeSquare p)) :=
  (contact_gaussian_sum ht).1.subtype _

theorem contact_heat_subtract_zero {t : ℝ} (ht : 0 < t) :
    contactHeatTrace t = normalTheta t 0 ^ 4 - 1 := by
  let f := fun p : Fin 4 → ℤ => Real.exp (-t*(∑ i, (p i:ℝ)^2))
  have hs : Summable f := (contact_gaussian_sum ht).1
  have he := hs.tsum_subtype_add_tsum_subtype_compl ({0}:Set (Fin 4 → ℤ))
  have h0 : (∑' p : ({0}:Set (Fin 4 → ℤ)), f p) = 1 := by
    rw [tsum_eq_single (⟨0,rfl⟩ : ({0}:Set (Fin 4 → ℤ))) (fun x hx => (hx (Subtype.ext x.property)).elim)]
    simp [f]
  rw [h0,(contact_gaussian_sum ht).2] at he
  change 1+contactHeatTrace t = _ at he
  linarith

/-- Explicit two-sided t⁻² bounds on the positive-width, zero-mode-subtracted
four-torus trace, and a uniform bound beyond unit heat width. -/
theorem contact_heat_bounds {t : ℝ} (ht : 0 < t) :
    (t ≤ 1 → (Real.pi^2-1)*t⁻¹^2 ≤ contactHeatTrace t ∧
      contactHeatTrace t ≤ (Real.pi^2*(normalTheta 1 0)^4)*t⁻¹^2) ∧
    (1 ≤ t → contactHeatTrace t ≤ (normalTheta 1 0)^4) := by
  rw [contact_heat_subtract_zero ht]
  constructor
  · intro h1
    obtain ⟨hl,hu⟩ := contact_theta_small ht h1
    have hs : (Real.sqrt (Real.pi/t))^4 = Real.pi^2*t⁻¹^2 := by
      rw [show 4=2*2 by decide,pow_mul,Real.sq_sqrt (by positivity)]
      ring
    have h₁ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hl 4
    have h₂ := pow_le_pow_left₀ ((Real.sqrt_nonneg _).trans hl) hu 4
    rw [hs] at h₁
    rw [mul_pow,hs] at h₂
    have hh : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr h1
    constructor <;> nlinarith [one_le_pow₀ hh (n := 2)]
  · intro h
    exact (sub_le_self _ zero_le_one).trans (pow_le_pow_left₀ ((zero_le_one).trans (contact_theta_one ht))
      (contact_theta_mono zero_lt_one h) 4)

private instance : Infinite CurvatureMode := by
  let v := fun n : ℕ => (fun _ : Fin 4 => (n:ℤ)+1)
  have hv n : v n ≠ 0 := by
    intro h
    have hh := congrFun h 0
    dsimp [v] at hh
    omega
  apply Infinite.of_injective (fun n : ℕ => (⟨v n,hv n⟩ : CurvatureMode))
  intro a b h
  have hh := congrArg (fun x : CurvatureMode => x.val 0) h
  dsimp [v] at hh
  omega

def contactHeatE (t : ℝ≥0) : ℝ≥0∞ :=
  ∑' p : CurvatureMode, ENNReal.ofReal (Real.exp (-(t:ℝ)*contactModeSquare p))

private theorem contact_heat_e_measurable : Measurable contactHeatE :=
  Measurable.ennreal_tsum fun p => (show Continuous (fun t : ℝ≥0 => Real.exp (-(t:ℝ)*contactModeSquare p)) by fun_prop).measurable.ennreal_ofReal

private theorem contact_heat_e_zero : contactHeatE 0 = ⊤ := by
  simp [contactHeatE]

private theorem contact_heat_e_pos {t : ℝ≥0} (ht : 0 < t) :
    contactHeatE t = ENNReal.ofReal (contactHeatTrace t) :=
  (ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) (contact_heat_summable ht)).symm

/-- Exact criterion for a finite positive Laplace law: the local curvature
budget is finite exactly if the atom at zero vanishes and the small-width
inverse second moment exists. Nonnegative integration keeps the cost at
zero infinite, including for distributions without a density. -/
theorem contact_laplace_inverse_second (ρ : Measure ℝ≥0) [IsFiniteMeasure ρ] :
    (∑' p : CurvatureMode, ∫⁻ t, ENNReal.ofReal (Real.exp (-(t:ℝ)*contactModeSquare p)) ∂ρ) ≠ ⊤ ↔
      ρ {0} = 0 ∧ (∫⁻ t in Ioc (0:ℝ≥0) 1, ENNReal.ofReal ((t:ℝ)⁻¹^2) ∂ρ) ≠ ⊤ := by
  rw [←lintegral_tsum (fun p => (show Continuous (fun t : ℝ≥0 => Real.exp (-(t:ℝ)*contactModeSquare p)) by fun_prop).measurable.ennreal_ofReal.aemeasurable)]
  change (∫⁻ t, contactHeatE t ∂ρ) ≠ ⊤ ↔ _
  let G := (Ioc (0:ℝ≥0) 1).indicator (fun t => ENNReal.ofReal ((t:ℝ)⁻¹^2))
  have hG : Measurable G := (by fun_prop : Measurable (fun t : ℝ≥0 => ENNReal.ofReal ((t:ℝ)⁻¹^2))).indicator measurableSet_Ioc
  have he : (∫⁻ t, G t ∂ρ) = ∫⁻ t in Ioc (0:ℝ≥0) 1, ENNReal.ofReal ((t:ℝ)⁻¹^2) ∂ρ :=
    lintegral_indicator measurableSet_Ioc _
  rw [←he]
  constructor
  · intro hi
    constructor
    · apply measure_mono_null (t := {t | contactHeatE t = ⊤}) _ (measure_eq_top_of_lintegral_ne_top contact_heat_e_measurable.aemeasurable hi)
      intro t ht
      simpa only [mem_singleton_iff.mp ht] using contact_heat_e_zero
    · apply ne_top_of_le_ne_top hi (lintegral_mono (fun t => ?_))
      by_cases ht : t ∈ Ioc (0:ℝ≥0) 1
      · rw [contact_heat_e_pos ht.1]
        have hb := ((contact_heat_bounds (show 0 < (t:ℝ) from ht.1)).1 (show (t:ℝ) ≤ 1 from ht.2)).1
        have hh : 1 ≤ Real.pi^2-1 := by nlinarith [Real.pi_gt_three]
        exact (show G t = ENNReal.ofReal ((t:ℝ)⁻¹^2) by simp [G,ht]).le.trans
          (ENNReal.ofReal_le_ofReal ((by simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (sq_nonneg (t:ℝ)⁻¹) : (t:ℝ)⁻¹^2 ≤ _).trans hb))
      · simp [G,ht]
  · rintro ⟨h0,hi⟩
    let K := Real.pi^2*(normalTheta 1 0)^4
    let M := (normalTheta 1 0)^4
    have hpos : ∀ᵐ t ∂ρ, (0:ℝ≥0) < t := by
      rw [ae_iff]
      simpa using h0
    have hbound : ∀ᵐ t ∂ρ, contactHeatE t ≤ ENNReal.ofReal K * G t + ENNReal.ofReal M := by
      filter_upwards [hpos] with t ht
      rw [contact_heat_e_pos ht]
      obtain hb := contact_heat_bounds (show 0 < (t:ℝ) from ht)
      by_cases h1 : t ≤ 1
      · have hmem : t ∈ Ioc (0:ℝ≥0) 1 := ⟨ht,h1⟩
        apply (ENNReal.ofReal_le_ofReal (hb.1 h1).2).trans
        rw [ENNReal.ofReal_mul (show 0 ≤ Real.pi^2*(normalTheta 1 0)^4 by positivity)]
        simp [G,hmem,K]
      · exact (ENNReal.ofReal_le_ofReal (hb.2 (le_of_not_ge h1))).trans le_add_self
    apply ne_top_of_le_ne_top _ (lintegral_mono_ae hbound)
    rw [lintegral_add_left (measurable_const.mul hG),lintegral_const_mul _ hG,lintegral_const]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hi,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)⟩

private theorem contact_mode_square_pos (p : CurvatureMode) : 0 < contactModeSquare p := by
  obtain ⟨i,hi⟩ : ∃ i, p.val i ≠ 0 := by
    by_contra! h
    exact p.property (funext h)
  exact (by exact_mod_cast (sq_pos_of_ne_zero hi) : (0:ℝ)<(p.val i:ℝ)^2).trans_le
    (Finset.single_le_sum (f := fun j => (p.val j:ℝ)^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

/-- Π Φ/(2|p|²) in exterior-Gram coordinates, where
W*W/|p|² is the orthogonal transverse projector. -/
def contactProjectedPhoton (p : CurvatureMode) (Φ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (Φ/(2*(contactModeSquare p)^2) : ℝ) • ((contactExterior p)ᴴ*contactExterior p)

theorem contact_projected_budget (p : CurvatureMode) (Φ : ℝ) :
    contactModeSquare p*(contactProjectedPhoton p Φ).trace.re = (3/2:ℝ)*Φ := by
  have hl : (contactLongitudinal p).trace = (contactModeSquare p:ℂ) := by
    simp [Matrix.trace,contactLongitudinal,contactModeSquare,contactPhotonVector,pow_two]
  rw [contactProjectedPhoton,Matrix.trace_smul,contact_exterior_gram,Matrix.trace_sub,Matrix.trace_smul,
    Matrix.trace_one,hl]
  have hh : ((contactModeSquare p:ℂ) • ((Fintype.card (Fin 4) : ℕ):ℂ) - (contactModeSquare p:ℂ)) =
      ((3*contactModeSquare p:ℝ):ℂ) := by push_cast; norm_num; ring
  rw [hh,Complex.real_smul,←Complex.ofReal_mul,Complex.ofReal_re]
  field_simp [(contact_mode_square_pos p).ne']

theorem contact_projected_transverse (p : CurvatureMode) {Φ : ℝ} (hΦ : 0 ≤ Φ) :
    (contactProjectedPhoton p Φ).PosSemidef ∧
    contactProjectedPhoton p Φ *ᵥ contactPhotonVector p = 0 := by
  constructor
  · exact (Matrix.posSemidef_conjTranspose_mul_self _).smul (show 0 ≤ Φ / (2*(contactModeSquare p)^2) by positivity)
  · have hz : contactExterior p *ᵥ contactPhotonVector p = 0 := by
      ext i
      fin_cases i <;> simp [contactExterior,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring
    rw [contactProjectedPhoton,Matrix.smul_mulVec,←Matrix.mulVec_mulVec,hz,Matrix.mulVec_zero,smul_zero]

def contactLaplaceReadout (ρ : Measure ℝ≥0) (p : CurvatureMode) :=
  ∫ t, Real.exp (-(t:ℝ)*contactModeSquare p) ∂ρ

/-- The factor 3/2 comes from the transverse rank three and the prescribed
factor 1/(2|p|²), before integrating the heat width. -/
theorem contact_projected_laplace_criterion (ρ : Measure ℝ≥0) [IsFiniteMeasure ρ] :
    Summable (fun p => contactModeSquare p*(contactProjectedPhoton p (contactLaplaceReadout ρ p)).trace.re) ↔
    ρ {0} = 0 ∧ (∫⁻ t in Ioc (0:ℝ≥0) 1, ENNReal.ofReal ((t:ℝ)⁻¹^2) ∂ρ) ≠ ⊤ := by
  have hp p : Integrable (fun t : ℝ≥0 => Real.exp (-(t:ℝ)*contactModeSquare p)) ρ := by
    apply (integrable_const (1:ℝ)).mono'
    · exact (show Continuous (fun t : ℝ≥0 => Real.exp (-(t:ℝ)*contactModeSquare p)) by fun_prop).aestronglyMeasurable
    · apply ae_of_all
      intro t
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg) (contact_mode_square_pos p).le
  have he p : ENNReal.ofReal (contactLaplaceReadout ρ p) =
      ∫⁻ t, ENNReal.ofReal (Real.exp (-(t:ℝ)*contactModeSquare p)) ∂ρ :=
    ofReal_integral_eq_lintegral_ofReal (hp p) (ae_of_all _ fun _ => (Real.exp_pos _).le)
  have hn p : 0 ≤ contactLaplaceReadout ρ p := integral_nonneg fun _ => (Real.exp_pos _).le
  rw [←contact_laplace_inverse_second]
  simp_rw [contact_projected_budget,←he]
  constructor
  · intro h
    have hh := h.mul_left (2/3:ℝ)
    have hc : Summable (contactLaplaceReadout ρ) := by
      convert hh using 1; funext p; ring
    rw [←ENNReal.ofReal_tsum_of_nonneg hn hc]
    exact ENNReal.ofReal_ne_top
  · intro h
    have hh := ENNReal.summable_toReal h
    have hc : Summable (contactLaplaceReadout ρ) := by
      simpa only [ENNReal.toReal_ofReal (hn _)] using hh
    exact hc.mul_left _

end UV
