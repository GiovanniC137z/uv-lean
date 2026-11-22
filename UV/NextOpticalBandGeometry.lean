import UV.NextOpticalRadial

/-! The compact invariant mass band of the exact massive pair has bounded
transverse radius and two positive longitudinal momentum fractions. The
calculation uses the future energy sign on the fixed intrinsic plane. -/

noncomputable section

open scoped InnerProductSpace

namespace UV.NextOpticalRadial

/-- The spatial component perpendicular to a specified unit transfer axis. -/
def transverseMomentum (n : SectorPlane.UnitVector ChargeSpatialMomentum)
    (k : ChargeSpatialMomentum) : ChargeSpatialMomentum :=
  k - ⟪k, (n : ChargeSpatialMomentum)⟫_ℝ • (n : ChargeSpatialMomentum)

theorem transverseMomentum_sq (n : SectorPlane.UnitVector ChargeSpatialMomentum)
    (k : ChargeSpatialMomentum) :
    ‖transverseMomentum n k‖^2 = ‖k‖^2 - ⟪k,(n : ChargeSpatialMomentum)⟫_ℝ ^ 2 := by
  unfold transverseMomentum
  rw [norm_sub_sq_real, norm_smul, n.property, mul_one, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right]
  ring

theorem transverseMomentum_add_axis (n : SectorPlane.UnitVector ChargeSpatialMomentum)
    (k : ChargeSpatialMomentum) (R : ℝ) :
    transverseMomentum n (k+R • (n : ChargeSpatialMomentum)) = transverseMomentum n k := by
  unfold transverseMomentum
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, n.property]
  simp only [one_pow, mul_one, add_smul]
  abel

theorem transverseMomentum_neg (n : SectorPlane.UnitVector ChargeSpatialMomentum)
    (k : ChargeSpatialMomentum) : transverseMomentum n (-k) = -transverseMomentum n k := by
  unfold transverseMomentum
  rw [inner_neg_left, neg_smul]
  abel

/-- Positive constituent longitudinal fractions follow directly from the
same pair mass shells, without any hypothesis on a boost of the spin data. -/
theorem compactBand_longitudinal_and_transverse
    (n : SectorPlane.UnitVector ChargeSpatialMomentum) (k : ChargeSpatialMomentum)
    {m S s₂ : ℝ} (hm : 0 < m) (hS : 0 < S) (hs : 0 < s₂)
    (hLarge : s₂ / m ≤ S)
    (hBand : (FurtherOptical.energy m (k+S • (n : ChargeSpatialMomentum)) +
      FurtherOptical.energy m (-k))^2-S^2 ≤ s₂) :
    let x₁ := ⟪k+S • (n : ChargeSpatialMomentum),(n : ChargeSpatialMomentum)⟫_ℝ
    let x₂ := ⟪-k,(n : ChargeSpatialMomentum)⟫_ℝ
    let c := m^2/(2*s₂)
    c*S ≤ x₁ ∧ x₁ ≤ S ∧ c*S ≤ x₂ ∧ x₂ ≤ S ∧
      ‖transverseMomentum n k‖^2 ≤ s₂/4 := by
  dsimp only
  let q₁ := k+S • (n : ChargeSpatialMomentum)
  let q₂ := -k
  let x₁ := ⟪q₁,(n : ChargeSpatialMomentum)⟫_ℝ
  let x₂ := ⟪q₂,(n : ChargeSpatialMomentum)⟫_ℝ
  let M₂ := m^2 + ‖transverseMomentum n k‖^2
  let E₁ := FurtherOptical.energy m q₁
  let E₂ := FurtherOptical.energy m q₂
  let D := E₁+E₂
  let c := m^2/(2*s₂)
  change c*S ≤ x₁ ∧ x₁ ≤ S ∧ c*S ≤ x₂ ∧ x₂ ≤ S ∧ ‖transverseMomentum n k‖^2 ≤ s₂/4
  have hx : x₁+x₂ = S := by
    dsimp [x₁,x₂,q₁,q₂]
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, n.property, inner_neg_left]
    ring
  have he₁ : E₁^2 = x₁^2+M₂ := by
    rw [show M₂ = m^2+‖transverseMomentum n q₁‖^2 by
      dsimp only [M₂,q₁]; rw [transverseMomentum_add_axis],
      show E₁^2 = m^2 + ‖q₁‖^2 from FurtherOptical.energy_sq .., transverseMomentum_sq]
    dsimp only [x₁]
    ring
  have he₂ : E₂^2 = x₂^2+M₂ := by
    rw [show M₂ = m^2+‖transverseMomentum n q₂‖^2 by
      dsimp only [M₂,q₂]; rw [transverseMomentum_neg, norm_neg],
      show E₂^2 = m^2 + ‖q₂‖^2 from FurtherOptical.energy_sq .., transverseMomentum_sq]
    dsimp only [x₂]
    ring
  have hM : 0 < M₂ := by dsimp [M₂]; positivity
  have hE₁ : 0 < E₁ := FurtherOptical.energy_pos hm q₁
  have hE₂ : 0 < E₂ := FurtherOptical.energy_pos hm q₂
  have ha₁ : |x₁| < E₁ := by
    apply (sq_lt_sq₀ (abs_nonneg _) hE₁.le).mp
    rw [sq_abs, he₁]
    linarith
  have ha₂ : |x₂| < E₂ := by
    apply (sq_lt_sq₀ (abs_nonneg _) hE₂.le).mp
    rw [sq_abs, he₂]
    linarith
  have hd : S < D := by
    dsimp only [D]
    linarith [(le_abs_self x₁).trans_lt ha₁, (le_abs_self x₂).trans_lt ha₂]
  have hcs : x₁*x₂+M₂ ≤ E₁*E₂ := by
    by_cases h : 0 ≤ x₁*x₂+M₂
    · apply (sq_le_sq₀ h (mul_nonneg hE₁.le hE₂.le)).mp
      rw [mul_pow, he₁, he₂]
      nlinarith [mul_nonneg hM.le (sq_nonneg (x₁-x₂))]
    · exact (le_of_lt (lt_of_not_ge h)).trans (mul_nonneg hE₁.le hE₂.le)
  have hMupper : 4*M₂ ≤ s₂ := by
    change D^2-S^2 ≤ s₂ at hBand
    dsimp only [D] at hBand
    rw [← hx] at hBand
    nlinarith [he₁, he₂, hcs]
  have hGap : D-S ≤ s₂/(2*S) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*S)).2
    change D^2-S^2 ≤ s₂ at hBand
    nlinarith [sq_nonneg (D-S)]
  have hMajor : m^2 ≤ M₂ := by dsimp [M₂]; linarith [sq_nonneg ‖transverseMomentum n k‖]
  have hLarge' : s₂ ≤ m*S := by
    rwa [div_le_iff₀ hm, mul_comm] at hLarge
  have hSmall : s₂/(2*S) ≤ (m^2/s₂)*S := by
    apply (div_le_iff₀ (by positivity : 0 < 2*S)).2
    have h := (sq_le_sq₀ hs.le (mul_nonneg hm.le hS.le)).2 hLarge'
    have h' : s₂^2 ≤ m^2*S^2 := by simpa only [mul_pow] using h
    have hz : s₂ ≤ (2*m^2*S^2)/s₂ :=
      (le_div_iff₀ hs).2 (by nlinarith [mul_nonneg (sq_nonneg m) (sq_nonneg S)])
    convert hz using 1
    ring
  have hfrac (x E : ℝ) (habs : |x| < E) (hE : E^2 = x^2+M₂) (hΔ : E-x ≤ D-S) :
      c*S ≤ x := by
    have hPlus : 0 < E+x := by linarith [neg_le_abs x]
    have hmass : m^2 ≤ (s₂/(2*S))*(E+x) := by
      calc
        _ ≤ M₂ := hMajor
        _ = (E-x)*(E+x) := by linear_combination -hE
        _ ≤ _ := mul_le_mul_of_nonneg_right (hΔ.trans hGap) hPlus.le
    have hxplus : (2*m^2/s₂)*S ≤ E+x := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hs).2
      rw [div_mul_eq_mul_div] at hmass
      have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 2*S)).1 hmass
      linarith
    have hxminus := hΔ.trans (hGap.trans hSmall)
    dsimp only [c]
    nlinarith [show (2*m^2/s₂)*S = 2*((m^2/s₂)*S) by ring,
      show m^2/(2*s₂)*S = ((m^2/s₂)*S)/2 by field_simp]
  have h₁ := hfrac x₁ E₁ ha₁ he₁ (by
    dsimp only [D]
    linarith [(le_abs_self x₂).trans_lt ha₂])
  have h₂ := hfrac x₂ E₂ ha₂ he₂ (by
    dsimp only [D]
    linarith [(le_abs_self x₁).trans_lt ha₁])
  have hcs₀ : 0 ≤ c*S := by dsimp [c]; positivity
  refine ⟨h₁, ?_, h₂, ?_, ?_⟩
  · linarith [hcs₀.trans h₂]
  · linarith [hcs₀.trans h₁]
  · dsimp only [M₂] at hMupper
    linarith [sq_nonneg m]

end UV.NextOpticalRadial
