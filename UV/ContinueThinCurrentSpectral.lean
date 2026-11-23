import UV.ContinueThinCurrent
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-! The coefficient's positive spectral bound and divergence of the
quadratic response once the thin-current shell has its perimeter mass. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators NNReal

namespace UV

/-- The positive unsubtracted spectral transform for the tested
transverse current. The mass-squared parameter lives in `ℝ≥0`. -/
def thinCurrentSpectrum (ρ : Measure ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ s, ENNReal.ofReal (1 / (x + (s : ℝ))) ∂ρ

/-- A nonzero positive spectrum gives a positive finite resolvent floor
from a bounded interval of squared masses. -/
theorem thinCurrentSpectrum_has_floor (ρ : Measure ℝ≥0) (hρ : ρ ≠ 0) :
    ∃ Z M : ℝ, 0 < Z ∧ 0 ≤ M ∧ ∀ x : ℝ, 0 < x →
      ENNReal.ofReal (Z / (x + M)) ≤ thinCurrentSpectrum ρ x := by
  have hall : (⋃ n : ℕ, Iic (n : ℝ≥0)) = univ := by
    apply Set.eq_univ_of_forall
    intro s
    obtain ⟨n, hn⟩ := exists_nat_ge (s : ℝ)
    exact Set.mem_iUnion.mpr ⟨n, show (s : ℝ) ≤ n from hn⟩
  have hpos : ∃ n : ℕ, ρ (Iic (n : ℝ≥0)) ≠ 0 := by
    by_contra! hn
    apply hρ
    apply Measure.measure_univ_eq_zero.mp
    rw [← hall]
    exact measure_iUnion_null hn
  obtain ⟨n, hn⟩ := hpos
  let a : ℝ≥0∞ := min 1 (ρ (Iic (n : ℝ≥0)))
  have ha0 : 0 < a := lt_min zero_lt_one (pos_iff_ne_zero.mpr hn)
  have hat : a ≠ ⊤ := (min_le_left _ _ |>.trans_lt ENNReal.one_lt_top).ne
  refine ⟨a.toReal, n, ENNReal.toReal_pos ha0.ne' hat, Nat.cast_nonneg _, fun x hx => ?_⟩
  have hrestrict : ENNReal.ofReal (1 / (x + (n : ℝ))) * ρ (Iic (n : ℝ≥0)) ≤
      thinCurrentSpectrum ρ x := by
    rw [← Measure.restrict_apply_univ, ← lintegral_const]
    apply le_trans (lintegral_mono_ae ?_) (lintegral_mono' Measure.restrict_le_self le_rfl)
    filter_upwards [ae_restrict_mem (μ := ρ) measurableSet_Iic] with s hs
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_left zero_le_one (by
      exact add_pos_of_pos_of_nonneg hx s.coe_nonneg)
      (add_le_add_left (show (s : ℝ) ≤ n from hs) x)
  calc
    _ = a * ENNReal.ofReal (1 / (x + (n : ℝ))) := by
      rw [show a = ENNReal.ofReal a.toReal from (ENNReal.ofReal_toReal hat).symm]
      rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.toReal_ofReal ENNReal.toReal_nonneg, div_eq_mul_one_div]
    _ ≤ ENNReal.ofReal (1 / (x + (n : ℝ))) * ρ (Iic (n : ℝ≥0)) := by
      rw [mul_comm]
      exact mul_le_mul_left' (min_le_right _ _) _
    _ ≤ _ := hrestrict

/-- Common Lebesgue normalization in four momentum dimensions. -/
def thinCurrentMomentumMeasure : Measure ThinCurrentPlane :=
  ENNReal.ofReal (((2 * Real.pi) ^ 4)⁻¹) • volume

/-- The actual momentum shell of the squared arclength current. -/
def thinCurrentShell {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment) (φ : ThinCurrentPlane → ℝ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (φ (R⁻¹ • p) * thinCurrentNormSq edges p) ∂thinCurrentMomentumMeasure

/-- The quadratic response with the actual transverse spectral data. -/
def thinCurrentResponse {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment) (G : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ p, G (‖p‖ ^ 2) * ENNReal.ofReal (thinCurrentNormSq edges p) ∂thinCurrentMomentumMeasure

/-- A spectral floor bounds each cut-off shell by a multiple of the
quadratic response. The factor is quadratic in the shell radius. -/
theorem thinCurrentShell_le_response {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment) (φ : ThinCurrentPlane → ℝ) (G : ℝ → ℝ≥0∞)
    {B Z M R : ℝ} (hB : 0 ≤ B) (hupper : ∀ p, φ p ≤ B)
    (hsupport : ∀ p, φ p ≠ 0 → 1 < ‖p‖ ∧ ‖p‖ < 2)
    (hZ : 0 < Z) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (hG : ∀ x : ℝ, 0 < x → ENNReal.ofReal (Z / (x + M)) ≤ G x) :
    thinCurrentShell edges φ R ≤
      ENNReal.ofReal (B * ((4 + M) * R ^ 2) / Z) * thinCurrentResponse edges G := by
  rw [thinCurrentShell, thinCurrentResponse, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro p
  have hp0 := thinCurrentNormSq_nonneg edges p
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  by_cases hw : φ (R⁻¹ • p) = 0
  · simp [hw]
  · have hx := hsupport _ hw
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR0), ← div_eq_inv_mul,
      lt_div_iff₀ hR0, div_lt_iff₀ hR0] at hx
    have hp : 0 < ‖p‖ ^ 2 := pow_pos ((one_mul R ▸ hR0).trans hx.1) 2
    have hkn : ‖p‖ ^ 2 + M ≤ (4 + M) * R ^ 2 := by
      have hnorm : ‖p‖ ^ 2 ≤ (2 * R)^2 := pow_le_pow_left₀ (norm_nonneg _) hx.2.le _
      have h1 : 1 ≤ R ^ 2 := by nlinarith
      nlinarith [mul_nonneg hM (sub_nonneg.mpr h1)]
    have hden : 0 < ‖p‖ ^ 2 + M := add_pos_of_pos_of_nonneg hp hM
    have hc : 0 ≤ B * ((4 + M) * R ^ 2) / Z := by positivity
    have hfloor := hG _ hp
    calc
      _ ≤ ENNReal.ofReal (B * thinCurrentNormSq edges p) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hupper _) hp0)
      _ = ENNReal.ofReal B * ENNReal.ofReal (thinCurrentNormSq edges p) :=
        ENNReal.ofReal_mul hB
      _ ≤ ENNReal.ofReal (B * ((4 + M) * R ^ 2) / Z) *
          (ENNReal.ofReal (Z / (‖p‖ ^ 2 + M)) * ENNReal.ofReal (thinCurrentNormSq edges p)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc]
        apply mul_le_mul_right'
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hden).mpr
        calc
          B * (‖p‖ ^ 2 + M) ≤ B * ((4 + M) * R ^ 2) := mul_le_mul_of_nonneg_left hkn hB
          _ = (B * ((4 + M) * R ^ 2) / Z) * Z := by rw [div_mul_cancel₀ _ hZ.ne']
      _ ≤ _ := mul_le_mul_left' (mul_le_mul_right' hfloor _) _

/-- A positive cubic shell asymptotic forces infinite quadratic
response for every nonzero positive unsubtracted spectrum. -/
theorem thinCurrentResponse_eq_top_of_shell_limit {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment) (φ : ThinCurrentPlane → ℝ) (ρ : Measure ℝ≥0)
    (hρ : ρ ≠ 0) {B c : ℝ} (hB : 0 ≤ B) (hupper : ∀ p, φ p ≤ B)
    (hsupport : ∀ p, φ p ≠ 0 → 1 < ‖p‖ ∧ ‖p‖ < 2) (hc : 0 < c)
    (hlim : Tendsto (fun R : ℝ => (thinCurrentShell edges φ R).toReal / R^3) atTop (𝓝 c)) :
    thinCurrentResponse edges (thinCurrentSpectrum ρ) = ⊤ := by
  by_contra hQ
  obtain ⟨Z, M, hZ, hM, hG⟩ := thinCurrentSpectrum_has_floor ρ hρ
  let A := B * (4 + M) / Z * (thinCurrentResponse edges (thinCurrentSpectrum ρ)).toReal
  have he : ∀ᶠ R : ℝ in atTop,
      c / 2 < (thinCurrentShell edges φ R).toReal / R^3 ∧ 1 ≤ R := by
    filter_upwards [hlim (Ioi_mem_nhds (show c / 2 < c by linarith)), eventually_ge_atTop 1]
      with R hR hR'
    exact ⟨hR, hR'⟩
  obtain ⟨R, ⟨hr, hR⟩, hlarge⟩ :=
    (he.and (eventually_gt_atTop (2 * A / c))).exists
  have h1 := thinCurrentShell_le_response edges φ _ hB hupper hsupport hZ hM hR hG
  have hz : 0 ≤ B * ((4 + M) * R ^ 2) / Z := by positivity
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQ) h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hz] at h2
  have ht : (thinCurrentShell edges φ R).toReal ≤ A * R ^ 2 := by
    convert h2 using 1
    unfold A
    ring
  have hp : 0 < R := zero_lt_one.trans_le hR
  have hr' := (lt_div_iff₀ (pow_pos hp 3)).mp hr
  have hl' := (div_lt_iff₀ hc).mp hlarge
  have hA : A < c / 2 * R := by linarith
  have hf := mul_lt_mul_of_pos_right hA (pow_pos hp 2)
  nlinarith

end UV
