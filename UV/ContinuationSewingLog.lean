import UV.ContinuationSewing
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Quantitative truncated integral version of the finite-difference
obstruction. No spectral reconstruction or ultraviolet limit is presumed. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace UV.ContinuationSewing

open UV.RevisionSpectrum (reciprocalDiff)

private theorem int_abs_mono {K : ℝ → ℝ} {a a' b b' : ℝ}
    (hab : a ≤ b) (hab' : a' ≤ b') (ha : a' ≤ a) (hb : b ≤ b')
    (hK : IntervalIntegrable K volume a' b') :
    (∫ x in a..b, |K x|) ≤ ∫ x in a'..b', |K x| := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab']
  exact setIntegral_mono_set ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab').mp hK.abs)
    (Eventually.of_forall fun x => abs_nonneg _) (Eventually.of_forall (Ioc_subset_Ioc ha hb))

private theorem trunc_mul_abs_bound (K : ℝ → ℝ) {r B k : ℝ} (hr : 0 < r)
    (hB : r ≤ B) (hk : 1 ≤ k) (hK : IntervalIntegrable K volume r (k*B)) :
    IntervalIntegrable (fun x => K (k*x)) volume r B ∧
      (∫ x in r..B, |K (k*x)|) ≤ ∫ x in r..(k*B), |K x| := by
  have hk₀ : 0 < k := zero_lt_one.trans_le hk
  have hrk : r ≤ k*r := by nlinarith [mul_nonneg (sub_nonneg.mpr hk) hr.le]
  have hkk : k*r ≤ k*B := mul_le_mul_of_nonneg_left hB hk₀.le
  have hIk : IntervalIntegrable K volume (k*r) (k*B) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hkk).mpr
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (hrk.trans hkk)).mp hK).mono_set
      (Ioc_subset_Ioc hrk le_rfl)
  constructor
  · have ht := hIk.comp_mul_left (c:=k)
    simpa only [mul_div_cancel_left₀ _ hk₀.ne'] using ht
  · rw [intervalIntegral.integral_comp_mul_left (fun y => |K y|) hk₀.ne', smul_eq_mul]
    have hI : 0 ≤ ∫ x in (k*r)..(k*B), |K x| :=
      intervalIntegral.integral_nonneg hkk (fun x _ => abs_nonneg (K x))
    calc
      _ ≤ ∫ x in (k*r)..(k*B), |K x| := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hk) hI
      _ ≤ _ := int_abs_mono hkk (hrk.trans hkk) hrk le_rfl hK

theorem reciprocalDiff_truncated_bound (K : ℝ → ℝ) {r B : ℝ} (hr : 0 < r)
    (hB : r ≤ B) (hK : ∀ b ≥ r, IntervalIntegrable K volume r b) (n : ℕ)
    (k : ℝ) (hk : 1 ≤ k) :
    IntervalIntegrable (fun x => reciprocalDiff x n K (k*x)) volume r B ∧
      (∫ x in r..B, |reciprocalDiff x n K (k*x)|)
        ≤ 2^n * ∫ x in r..((k+n)*B), |K x| := by
  have hB₀ : 0 < B := hr.trans_le hB
  induction n generalizing k with
  | zero =>
    have hkr : r ≤ k*B := hB.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hk) hB₀.le])
    simpa [reciprocalDiff] using trunc_mul_abs_bound K hr hB hk (hK (k*B) hkr)
  | succ n ih =>
    have hl : 1 ≤ k+1 := by linarith
    obtain ⟨hi₁, hh₁⟩ := ih k hk
    obtain ⟨hi₂, hh₂⟩ := ih (k+1) hl
    have hr₁ : r ≤ (k+n)*B := hB.trans (by
      have hx : 0 ≤ (k+(n:ℝ))-1 := by linarith
      nlinarith [mul_nonneg hx hB₀.le])
    have hrew : k + (n+1:ℕ) = k+1+(n:ℝ) := by push_cast; ring
    have hEnd : (k+(n:ℝ))*B ≤ (k+(n+1:ℕ))*B := by
      rw [hrew]
      nlinarith
    have hmon := int_abs_mono hr₁ (hr₁.trans hEnd) le_rfl hEnd
      (hK ((k+(n+1:ℕ))*B) (hr₁.trans hEnd))
    let F := fun x => reciprocalDiff x n K (k*x)
    let G := fun x => reciprocalDiff x n K ((k+1)*x)
    have heq : (fun x => reciprocalDiff x (n+1) K (k*x)) = fun x => F x-G x := by
      funext x
      simp [reciprocalDiff, F, G, add_mul]
    have hi : IntervalIntegrable (fun x => F x-G x) volume r B := hi₁.sub hi₂
    refine ⟨heq ▸ hi, ?_⟩
    have heq' (x : ℝ) : reciprocalDiff x (n+1) K (k*x) = F x-G x :=
      congrFun heq x
    simp only [heq']
    calc
      _ ≤ ∫ x in r..B, |F x|+|G x| :=
        intervalIntegral.integral_mono_on hB hi.abs (hi₁.abs.add hi₂.abs)
          (fun x _ => abs_sub _ _)
      _ = (∫ x in r..B, |F x|) + ∫ x in r..B, |G x| :=
        intervalIntegral.integral_add hi₁.abs hi₂.abs
      _ ≤ _ := by
        rw [← hrew] at hh₂
        have hh₁' := hh₁.trans (mul_le_mul_of_nonneg_left hmon (by positivity : 0 ≤ (2:ℝ)^n))
        rw [pow_succ]
        linarith

/-- The finite-difference inverse tail forces logarithmic growth of
the cumulative absolute response. -/
theorem reciprocalDiff_truncated_log_lower (K : ℝ → ℝ) {c r B : ℝ}
    (hr : 0 < r) (hB : r ≤ B)
    (hK : ∀ b ≥ r, IntervalIntegrable K volume r b) (n : ℕ)
    (hlower : ∀ x > r, c/x ≤ |reciprocalDiff x n K x|) :
    (c/(2^n))*(Real.log B-Real.log r) ≤
      ∫ x in r..((1+n)*B), |K x| := by
  have hBp : 0 < B := hr.trans_le hB
  obtain ⟨hi, he⟩ := reciprocalDiff_truncated_bound K hr hB hK n 1 le_rfl
  simp only [one_mul] at hi he
  have hri : IntervalIntegrable (fun x : ℝ => c*x⁻¹) volume r B := by
    apply ContinuousOn.intervalIntegrable
    have hpos : ∀ x ∈ uIcc r B, x ≠ 0 := by
      rw [uIcc_of_le hB]
      exact fun x hx => (hr.trans_le hx.1).ne'
    exact continuousOn_const.mul (continuousOn_id.inv₀ hpos)
  have hlow : (∫ x in r..B, c*x⁻¹) ≤ ∫ x in r..B, |reciprocalDiff x n K x| := by
    rw [intervalIntegral.integral_of_le hB, intervalIntegral.integral_of_le hB]
    apply setIntegral_mono_on hri.1 hi.abs.1 measurableSet_Ioc
    intro x hx
    simpa only [div_eq_mul_inv] using hlower x hx.1
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hr hBp,
    Real.log_div hBp.ne' hr.ne'] at hlow
  have hh := hlow.trans he
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < (2:ℝ)^n)]
  simpa only [mul_comm (2^n:ℝ)] using hh

/-- Explicit logarithmic lower growth for the contact-subtracted spectral
response when the finite radial intervals have ordinary integrals. -/
theorem contactSubtracted_log_lower (ρ : Measure ℝ) (P : Polynomial ℝ)
    (g : ℝ → Polynomial ℝ) (sign : ℝ) (hSign : sign ≠ 0) (n : ℕ)
    {R s₀ s₁ : ℝ} (hR : 0 < R) (hs₀ : 0 < s₀) (hxb : s₁ ≤ R)
    (hfin : ρ (Icc s₀ s₁) ≠ ⊤) (hpos : ρ (Icc s₀ s₁) ≠ 0)
    (hP : P.natDegree < n+1) (hs : ∀ᵐ s ∂ρ, 0 ≤ s)
    (hg : ∀ᵐ s ∂ρ, (g s).natDegree < n+1)
    (hf : ∀ x ≥ R, Integrable (fun s => x/(s+x) - (g s).eval x) ρ)
    (hK : ∀ b ≥ R, IntervalIntegrable (contactSubtractedResponse ρ P g sign) volume R b) :
    ∃ d > 0, ∀ B ≥ R, d*(Real.log B-Real.log R) ≤
      ∫ x in R..((1+(n+1:ℕ))*B), |contactSubtractedResponse ρ P g sign x| := by
  let d := |sign| * bandConstant n s₀ * ρ.real (Icc s₀ s₁)
  have hmass : 0 < ρ.real (Icc s₀ s₁) := ENNReal.toReal_pos hpos hfin
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos (mul_pos (abs_pos.mpr hSign) (bandConstant_pos hs₀ n)) hmass
  refine ⟨d/(2^(n+1)), by positivity, fun B hB => ?_⟩
  apply reciprocalDiff_truncated_log_lower (contactSubtractedResponse ρ P g sign) hR hB hK (n+1)
  intro x hx
  have hx' : 0 < x := hR.trans hx
  obtain ⟨hi, heq⟩ := difference_contactSubtractedResponse ρ P g sign hR hx'.le n hP hs hg hf x hx.le
  rw [heq]
  have h := differenceKernel_mass_lower ρ n hs₀ hx' (hxb.trans hx.le) hs hfin hi
  convert mul_le_mul_of_nonneg_left h (abs_nonneg sign) using 1; dsimp [d]; ring

/-- In the unsubtracted case the radial shell integral grows at least
linearly in the squared Euclidean radius. -/
theorem unsubtracted_shell_linear_lower (ρ : Measure ℝ) (D : ℝ → ℝ)
    (hs : ∀ᵐ s ∂ρ, 0 ≤ s) {s₀ s₁ c R B : ℝ}
    (hc : 0 < c) (hR : 0 < R) (hB : R ≤ B) (hb : s₁ ≤ R)
    (hmass : ρ (Icc s₀ s₁) ≠ ⊤)
    (hD : ∀ X ≥ R, c/X ≤ D X)
    (hInt : ∀ X ≥ R, Integrable (fun s => X/(s+X)) ρ)
    (hK : IntervalIntegrable (fun X => X*D X*∫ s, X/(s+X) ∂ρ) volume R B) :
    (B-R) * (c*(ρ.real (Icc s₀ s₁)/2)) ≤
      ∫ X in R..B, X*D X*∫ s, X/(s+X) ∂ρ := by
  let a := ρ.real (Icc s₀ s₁)/2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hi := intervalIntegral.integral_mono_on hB
    (intervalIntegrable_const (c := c*a)) hK (by
      intro x hx
      have hx₀ : 0 < x := hR.trans_le hx.1
      have hk := UV.RevisionSpectrum.positive_band_unsubtracted_lower ρ hs hx₀
        (hb.trans hx.1) hmass (hInt x hx.1)
      have hd : c ≤ x*D x := by
        have hh := (div_le_iff₀ hx₀).mp (hD x hx.1)
        linarith
      exact (mul_le_mul_of_nonneg_left hk hc.le).trans
        (mul_le_mul_of_nonneg_right hd (ha.trans hk)))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, a] using hi

end UV.ContinuationSewing
