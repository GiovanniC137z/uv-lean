import UV.UnboundedSourceResolution

/-! Bounded exponential identities for the supplied real Borel calculus.
Complex phases are built from its real and imaginary components. -/

noncomputable section

namespace UV

open MeasureTheory Filter Set
open scoped Topology Nat

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P : SourcePVM H}

/-- The complex spectral readout of a complex bounded Borel symbol. -/
def openingComplexBorel (C : SourceBorelCalculus P) (g : ℝ → ℂ) : H →L[ℂ] H :=
  C.operator (fun t => (g t).re) + Complex.I • C.operator (fun t => (g t).im)

private theorem opening.borel_one (C : SourceBorelCalculus P) :
    C.operator (fun _ => 1) = 1 := by
  simpa only [indicator_univ, P.univ] using C.indicator univ MeasurableSet.univ

private theorem opening.borel_pow (C : SourceBorelCalculus P) (f : ℝ → ℝ)
    (hf : sourceBoundedBorel f) (n : ℕ) :
    C.operator (fun t => f t ^ n) = C.operator f ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using opening.borel_one C
  | succ n ih =>
    have hb (k : ℕ) : sourceBoundedBorel (fun t => f t ^ k) := by
      induction k with
      | zero => simpa only [pow_zero] using sourceBoundedBorel_one
      | succ k ih => simpa only [pow_succ] using sourceBoundedBorel_mul ih hf
    simp_rw [pow_succ]
    rw [C.mul _ _ (hb n) hf, ih]

private theorem opening.borel_pow_bounded (f : ℝ → ℝ) (hf : sourceBoundedBorel f) (n : ℕ) :
    sourceBoundedBorel (fun t => f t ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using sourceBoundedBorel_one
  | succ n ih => simpa only [pow_succ] using sourceBoundedBorel_mul ih hf

private def opening.phasePartial (f : ℝ → ℝ) (a : ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N, (a ^ k / (k ! : ℂ)) * ((f t : ℂ) ^ k)

private theorem opening.borel_partial (C : SourceBorelCalculus P)
    (f : ℝ → ℝ) (hf : sourceBoundedBorel f) (a : ℂ) (N : ℕ) :
    openingComplexBorel C (opening.phasePartial f a N) =
      ∑ k ∈ Finset.range N, (a ^ k / (k ! : ℂ)) • C.operator f ^ k := by
  let b (k : ℕ) := a ^ k / (k ! : ℂ)
  have hre :
      (fun t => (opening.phasePartial f a N t).re) =
        (fun t => ∑ k ∈ Finset.range N, (b k).re * f t ^ k) := by
    funext t
    simp [opening.phasePartial, b, ← Complex.ofReal_pow, Complex.mul_re,
      Complex.re_sum]
  have him :
      (fun t => (opening.phasePartial f a N t).im) =
        (fun t => ∑ k ∈ Finset.range N, (b k).im * f t ^ k) := by
    funext t
    simp [opening.phasePartial, b, ← Complex.ofReal_pow, Complex.mul_im,
      Complex.im_sum, mul_comm]
  rw [openingComplexBorel, hre, him, sourceBorel_sum C, sourceBorel_sum C,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  · apply Finset.sum_congr rfl
    intro k _
    rw [C.smul _ _ (opening.borel_pow_bounded f hf k),
      C.smul _ _ (opening.borel_pow_bounded f hf k), opening.borel_pow C f hf,
      smul_smul, ← add_smul]
    congr 1
    rw [mul_comm Complex.I]
    exact Complex.re_add_im (b k)
  · exact fun k _ => sourceBoundedBorel_smul _ (opening.borel_pow_bounded f hf k)
  · exact fun k _ => sourceBoundedBorel_smul _ (opening.borel_pow_bounded f hf k)

private theorem opening.norm_phasePartial_le (f : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ t, |f t| ≤ B) (a : ℂ) (N : ℕ) (t : ℝ) :
    ‖opening.phasePartial f a N t‖ ≤ ∑' k : ℕ, (‖a‖ * B) ^ k / (k ! : ℝ) := by
  have hs := Real.summable_pow_div_factorial (‖a‖ * B)
  unfold opening.phasePartial
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum ?_).trans
    (hs.sum_le_tsum (Finset.range N) (fun _ _ => by positivity)))
  intro k _
  rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, mul_div_right_comm]
  gcongr
  exact hf t

private theorem opening.phasePartial_tendsto (f : ℝ → ℝ) (a : ℂ) (t : ℝ) :
    Tendsto (fun N => opening.phasePartial f a N t) atTop
      (𝓝 (Complex.exp (a * (f t : ℂ)))) := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  have h := (NormedSpace.expSeries_div_summable ℂ (a * (f t : ℂ))).hasSum.tendsto_sum_nat
  convert h using 1
  funext N
  unfold opening.phasePartial
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_pow]
  ring

/-- The Borel calculus of the exponential of a bounded real symbol is
the genuine Banach-algebra exponential of its bounded coordinate operator. -/
theorem openingBorel_exponential (C : SourceBorelCalculus P)
    (f : ℝ → ℝ) (hf : sourceBoundedBorel f) (a : ℂ) :
    openingComplexBorel C (fun t => Complex.exp (a * (f t : ℂ))) =
      NormedSpace.exp ℂ (a • C.operator f) := by
  obtain ⟨B, hB, hBf⟩ := hf.2
  let M := ∑' k : ℕ, (‖a‖ * B) ^ k / (k ! : ℝ)
  have hM : 0 ≤ M := tsum_nonneg fun _ => by positivity
  have hfmeas : Measurable f := hf.1
  have hg (N : ℕ) : Measurable (opening.phasePartial f a N) := by
    unfold opening.phasePartial
    fun_prop
  have he : Measurable (fun t => Complex.exp (a * (f t : ℂ))) := by
    fun_prop
  apply ContinuousLinearMap.ext
  intro v
  have hr := C.strong_limit (fun N t => (opening.phasePartial f a N t).re)
    (fun t => (Complex.exp (a * (f t : ℂ))).re) M
    (fun N => Complex.continuous_re.measurable.comp (hg N))
    (Complex.continuous_re.measurable.comp he) hM
    (fun N t => (Complex.abs_re_le_norm _).trans (opening.norm_phasePartial_le f hB hBf a N t))
    (fun t => Complex.continuous_re.continuousAt.tendsto.comp (opening.phasePartial_tendsto f a t)) v
  have hi := C.strong_limit (fun N t => (opening.phasePartial f a N t).im)
    (fun t => (Complex.exp (a * (f t : ℂ))).im) M
    (fun N => Complex.continuous_im.measurable.comp (hg N))
    (Complex.continuous_im.measurable.comp he) hM
    (fun N t => (Complex.abs_im_le_norm _).trans (opening.norm_phasePartial_le f hB hBf a N t))
    (fun t => Complex.continuous_im.continuousAt.tendsto.comp (opening.phasePartial_tendsto f a t)) v
  have hp : Tendsto (fun N => openingComplexBorel C (opening.phasePartial f a N) v)
      atTop (𝓝 (openingComplexBorel C (fun t => Complex.exp (a * (f t : ℂ))) v)) := by
    simpa only [openingComplexBorel, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply] using hr.add (hi.const_smul Complex.I)
  let ev : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H v
  have hs' := ev.hasSum (NormedSpace.expSeries_summable' (𝕂 := ℂ) (a • C.operator f)).hasSum
  have hs := hs'.tendsto_sum_nat
  have hsum : Tendsto (fun N => openingComplexBorel C (opening.phasePartial f a N) v)
      atTop (𝓝 ((NormedSpace.exp ℂ (a • C.operator f)) v)) := by
    rw [NormedSpace.exp_eq_tsum]
    apply hs.congr
    intro N
    rw [opening.borel_partial C f hf a, ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    have hcomm : Commute (algebraMap ℂ (H →L[ℂ] H) a) (C.operator f) := Algebra.commutes _ _
    have hpow : (a • C.operator f) ^ k = a ^ k • C.operator f ^ k := by
      rw [Algebra.smul_def a, hcomm.mul_pow, ← map_pow, ← Algebra.smul_def]
    rw [hpow, smul_smul, ← div_eq_inv_mul]
    rfl
  exact tendsto_nhds_unique hp hsum

end UV
