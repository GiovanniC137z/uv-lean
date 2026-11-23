import UV.RevisionSpectrumRigidity

/-! Normalization and the first spectral moment of a positive squared-energy
law from the two nonzero-frequency resolvent bounds. -/

noncomputable section

namespace UV.RadialPhoton

open MeasureTheory Set Filter
open scoped ENNReal Topology

def photonTransform (ρ : Measure ℝ) (x : ℝ) : ℝ := ∫ s, (x+s)⁻¹ ∂ρ

def PhotonSandwich (ρ : Measure ℝ) (a b : ℝ) : Prop :=
  ∀ x > 0, (x+b)⁻¹ ≤ photonTransform ρ x ∧ photonTransform ρ x ≤ (x+a)⁻¹

/-- No initial normalization or finite moment is required. -/
theorem photon_sandwich_moments (ρ : Measure ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hs : ∀ᵐ s ∂ρ, 0 ≤ s) (hi : ∀ x > 0, Integrable (fun s : ℝ => (x+s)⁻¹) ρ)
    (hG : PhotonSandwich ρ a b) :
    ρ univ = 1 ∧ Integrable (fun s : ℝ => s) ρ ∧ (∫ s, s ∂ρ) ∈ Icc a b := by
  let x := fun n : ℕ => (n:ℝ)+1
  have hx (n : ℕ) : 0 < x n := by dsimp [x]; positivity
  have hmono : Monotone x := fun _ _ h => add_le_add_right (Nat.cast_le.mpr h) _
  have htop : Tendsto x atTop atTop := tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hb := ha.trans hab
  have hT (n : ℕ) := hG (x n) (hx n)
  have hmass_lim : Tendsto (fun n => x n * photonTransform ρ (x n)) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (UV.RevisionSpectrum.normalizedKernel_tendsto hx htop b hb)
      (UV.RevisionSpectrum.normalizedKernel_tendsto hx htop a ha)
    · intro n
      dsimp only
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (hT n).1 (hx n).le
    · intro n
      dsimp only
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (hT n).2 (hx n).le
  have hmi (n : ℕ) : Integrable (fun s => x n/(x n+s)*(1:ℝ)) ρ := by
    simpa only [mul_one,div_eq_mul_inv] using (hi _ (hx n)).const_mul (x n)
  have hml : Tendsto (fun n => ∫ s, x n/(x n+s)*(1:ℝ) ∂ρ) atTop (𝓝 1) := by
    simpa only [mul_one,div_eq_mul_inv,integral_const_mul,photonTransform] using hmass_lim
  have hmass := UV.RevisionSpectrum.normalizedMoment_lintegral hx hmono htop hs
    (f := fun _ => 1) (Eventually.of_forall fun _ => zero_le_one) hmi hml
  have hρ : ρ univ = 1 := by simpa using hmass
  letI : IsProbabilityMeasure ρ := ⟨hρ⟩
  let K := fun n s => x n/(x n+s)*s
  let M := fun n => ∫ s, K n s ∂ρ
  have hKi (n : ℕ) : Integrable (K n) ρ := by
    refine (integrable_const (μ := ρ) (x n)).mono' (by dsimp [K]; fun_prop) ?_
    filter_upwards [hs] with s hs'
    have hp := add_pos_of_pos_of_nonneg (hx n) hs'
    change ‖x n/(x n+s)*s‖ ≤ x n
    rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg (hx n).le hp.le) hs'),div_mul_eq_mul_div,
      div_le_iff₀ hp]
    nlinarith only [sq_nonneg (x n)]
  have hMeq (n : ℕ) : M n = x n-(x n)^2*photonTransform ρ (x n) := by
    have he : K n =ᵐ[ρ] fun s => x n-(x n)^2*(x n+s)⁻¹ := by
      filter_upwards [hs] with s hs'
      have hne := (add_pos_of_pos_of_nonneg (hx n) hs').ne'
      dsimp [K]
      field_simp
      ring
    unfold M photonTransform
    rw [integral_congr_ae he, integral_sub (integrable_const _) ((hi _ (hx n)).const_mul _),
      integral_const_mul,integral_const]
    simp
  have hmid (n : ℕ) (d : ℝ) (hd : 0 ≤ d) :
      x n - (x n)^2*(x n+d)⁻¹ = x n/(x n+d)*d := by
    have hne := (add_pos_of_pos_of_nonneg (hx n) hd).ne'
    field_simp
    ring
  have hbound (n : ℕ) : x n/(x n+a)*a ≤ M n ∧ M n ≤ b := by
    rw [hMeq,← hmid n a ha]
    constructor
    · exact sub_le_sub_left (mul_le_mul_of_nonneg_left (hT n).2 (sq_nonneg _)) _
    · calc
        _ ≤ x n-(x n)^2*(x n+b)⁻¹ := sub_le_sub_left
          (mul_le_mul_of_nonneg_left (hT n).1 (sq_nonneg _)) _
        _ = _ := hmid n b hb
        _ ≤ b := mul_le_of_le_one_left hb ((div_le_one (add_pos_of_pos_of_nonneg (hx n) hb)).mpr
          (le_add_of_nonneg_right hb))
  have hM : Monotone M := by
    intro i j hij
    apply integral_mono_ae (hKi i) (hKi j)
    filter_upwards [hs] with s hs'
    apply mul_le_mul_of_nonneg_right _ hs'
    rw [div_le_div_iff₀ (add_pos_of_pos_of_nonneg (hx i) hs') (add_pos_of_pos_of_nonneg (hx j) hs')]
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hmono hij)) hs']
  have hlim := tendsto_atTop_ciSup hM (show BddAbove (range M) from
    ⟨b,fun y ⟨n,hn⟩ => hn ▸ (hbound n).2⟩)
  have hlow : a ≤ ⨆ n, M n := by
    have h := (UV.RevisionSpectrum.normalizedKernel_tendsto hx htop a ha).mul_const a
    rw [one_mul] at h
    exact le_of_tendsto_of_tendsto' h hlim fun n => (hbound n).1
  have hupp : (⨆ n, M n) ≤ b := ciSup_le fun n => (hbound n).2
  have hm := UV.RevisionSpectrum.normalizedMoment_lintegral hx hmono htop hs (f := fun s => s) hs hKi hlim
  have hI : Integrable (fun s : ℝ => s) ρ := (lintegral_ofReal_ne_top_iff_integrable
    measurable_id.aestronglyMeasurable hs).mp (hm ▸ ENNReal.ofReal_ne_top)
  have hE : (∫ s, s ∂ρ) = ⨆ n, M n := by
    rw [integral_eq_lintegral_of_nonneg_ae hs measurable_id.aestronglyMeasurable, hm,
      ENNReal.toReal_ofReal (ha.trans hlow)]
  exact ⟨hρ,hI,hE ▸ ⟨hlow,hupp⟩⟩

end UV.RadialPhoton
