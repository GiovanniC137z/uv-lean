import UV.VerifySpectrumCrossOscillation
import UV.RevisionSpectrumCross

/-! Direct Stieltjes evaluation for the shifted square-root cross family.
The spectral coordinate is the nonnegative mass squared on a fixed plane. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV.RevisionSpectrum

def verifyCrossCovariance (a M m₂ x : ℝ) : ℝ :=
  Real.exp (-a*(Real.sqrt (x+M^2)-M))/(x+m₂)

def verifyCrossResidue (a M m₂ : ℝ) : ℝ :=
  if m₂ ≤ M^2 then Real.exp (a*(M-Real.sqrt (M^2-m₂)))
  else Real.exp (a*M)*Real.cos (a*Real.sqrt (m₂-M^2))

/-- The literal removable continuum value at an admitted embedded pole.
The point value leaves the Lebesgue spectral measure unchanged. -/
def verifyCrossContinuum (a M m₂ s : ℝ) : ℝ :=
  if s = m₂ ∧ M^2 < m₂ then
    -(Real.exp (a*M)*(a/(2*Real.sqrt (m₂-M^2)))*Real.cos (a*Real.sqrt (m₂-M^2)))/Real.pi
  else crossDensity a M m₂ s

theorem verifyCrossContinuum_ae (a M m₂ : ℝ) :
    verifyCrossContinuum a M m₂ =ᵐ[volume] crossDensity a M m₂ := by
  have hne : ∀ᵐ s : ℝ, s ≠ m₂ := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using measure_singleton m₂
  filter_upwards [hne] with s hs
  simp [verifyCrossContinuum, hs]

theorem verifyCrossContinuum_embedded (a M m₂ : ℝ) (hm : M^2 < m₂)
    (hres : Real.sin (a*Real.sqrt (m₂-M^2)) = 0) :
    Tendsto (verifyCrossContinuum a M m₂) (𝓝[≠] m₂)
      (𝓝 (verifyCrossContinuum a M m₂ m₂)) := by
  simp only [verifyCrossContinuum, true_and, if_pos hm]
  apply (crossDensity_embedded_limit hm hres).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hn : s ≠ m₂ := hs
  exact (if_neg (fun h => hn h.1)).symm

private theorem verify_cross_spectral_integrable_iff (M₂ : ℝ) (f : ℝ → ℝ) :
    IntegrableOn f (Ioi M₂) ↔
      IntegrableOn (fun k : ℝ => (2*k)*f (k^2+M₂)) (Ioi 0) := by
  have hd : ∀ k ∈ Ioi (0:ℝ),
      HasDerivWithinAt (fun k : ℝ => k^2+M₂) (2*k) (Ioi 0) k := by
    intro k _
    simpa using (((hasDerivAt_id k).pow 2).add_const M₂).hasDerivWithinAt
  have hinj : InjOn (fun k : ℝ => k^2+M₂) (Ioi 0) := by
    apply StrictMonoOn.injOn
    intro r hr k hk h
    exact add_lt_add_right ((sq_lt_sq₀ hr.le hk.le).mpr h) M₂
  have he : (fun k : ℝ => k^2+M₂) '' Ioi 0 = Ioi M₂ := by
    ext s
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact (show M₂<k^2+M₂ by linarith [sq_pos_of_pos (mem_Ioi.mp hk)])
    · intro hs
      have h : 0<s-M₂ := sub_pos.mpr hs
      exact ⟨Real.sqrt (s-M₂),Real.sqrt_pos.mpr h, by
        change Real.sqrt (s-M₂)^2+M₂=s
        rw [Real.sq_sqrt h.le]
        ring⟩
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hd hinj f
  rw [he] at h
  rw [h]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with k hk
  have hk₀ : 0 < k := hk
  simp only [smul_eq_mul, abs_of_pos (show 0 < 2*k by positivity)]

private theorem verify_cross_pair_point {a M m₂ x w k : ℝ} (hk : 0 < k)
    (hw : w^2 = x+M^2) :
    (2*k)*(crossDensity a M m₂ (k^2+M^2)/(x+(k^2+M^2))) =
      -(2*Real.exp (a*M)/Real.pi) *
        (k*Real.sin (a*k)*((k^2+(M^2-m₂))⁻¹*(k^2+w^2)⁻¹)) := by
  have hcut : M^2 < k^2+M^2 := by linarith [sq_pos_of_pos hk]
  have hdiff : (k^2+M^2)-M^2 = k^2 := by ring
  have hpole : m₂-(k^2+M^2) = -(k^2+(M^2-m₂)) := by ring
  have hshift : x+(k^2+M^2) = k^2+w^2 := by rw [hw]; ring
  rw [crossDensity, if_pos hcut, hdiff, Real.sqrt_sq hk.le, hpole, hshift]
  simp only [div_eq_mul_inv, mul_inv, inv_neg]
  ring

private theorem verify_cross_pair_subthreshold {a M m₂ w : ℝ} (ha : 0 < a) (hw : 0 < w)
    (hm : m₂ < M^2) (hn : M^2-m₂ < w^2) :
    let c := Real.sqrt (M^2-m₂)
    IntegrableOn (fun k : ℝ => k*Real.sin (a*k)*((k^2+(M^2-m₂))⁻¹*(k^2+w^2)⁻¹))
      (Ioi 0) ∧
    (∫ k : ℝ in Ioi 0, k*Real.sin (a*k)*((k^2+(M^2-m₂))⁻¹*(k^2+w^2)⁻¹)) =
      (Real.pi/2)*(Real.exp (-c*a)-Real.exp (-w*a))/(w^2-(M^2-m₂)) := by
  dsimp only
  let c := Real.sqrt (M^2-m₂)
  have hc : 0<c := Real.sqrt_pos.mpr (by linarith)
  have hcs : c^2 = M^2-m₂ := Real.sq_sqrt (by linarith)
  have hcw : c ≠ w := by
    intro he
    rw [← he, hcs] at hn
    exact (lt_irrefl _ hn)
  exact ⟨by simpa only [hcs] using continuePairSin_integrable hc hw a,
    by simpa only [hcs] using continuePairSin_formula hc hw hcw ha⟩

private theorem verify_cross_pair_resonant {a M m₂ w : ℝ} (ha : 0 < a) (hw : 0 < w)
    (hm : M^2 ≤ m₂) (hs : Real.sin (a*Real.sqrt (m₂-M^2)) = 0) :
    let q := Real.sqrt (m₂-M^2)
    IntegrableOn (fun k : ℝ => k*Real.sin (a*k)*((k^2+(M^2-m₂))⁻¹*(k^2+w^2)⁻¹))
      (Ioi 0) ∧
    (∫ k : ℝ in Ioi 0, k*Real.sin (a*k)*((k^2+(M^2-m₂))⁻¹*(k^2+w^2)⁻¹)) =
      (Real.pi/2)*(Real.cos (a*q)-Real.exp (-w*a))/(w^2+(m₂-M^2)) := by
  dsimp only
  let q := Real.sqrt (m₂-M^2)
  have hq : 0≤q := Real.sqrt_nonneg _
  have hqs : q^2 = m₂-M^2 := Real.sq_sqrt (by linarith)
  have he (k : ℝ) : k^2 - (m₂-M^2) = k^2+(M^2-m₂) := by ring
  exact ⟨by simpa only [hqs, he] using verify_resonance_pair_integrable hw hq ha hs,
    by simpa only [hqs, he] using verify_resonance_pair_integral hw hq ha hs⟩

/-- The precise atom and continuum give the positive-Euclidean Stieltjes
transform by absolutely convergent integration in every admitted case. -/
theorem verify_cross_stieltjes {a M m₂ x : ℝ} (ha : 0<a) (hm₂ : 0≤m₂) (hx : 0<x)
    (hadm : m₂≤M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2))=0) :
    IntegrableOn (fun s : ℝ => verifyCrossContinuum a M m₂ s/(x+s)) (Ioi (M^2)) ∧
    verifyCrossResidue a M m₂/(x+m₂) +
      (∫ s : ℝ in Ioi (M^2), verifyCrossContinuum a M m₂ s/(x+s)) =
        verifyCrossCovariance a M m₂ x := by
  let w := Real.sqrt (x+M^2)
  have hwpos : 0<w := Real.sqrt_pos.mpr (by positivity)
  have hw : w^2=x+M^2 := Real.sq_sqrt (by positivity)
  let F := fun k : ℝ => k*Real.sin (a*k)*((k^2+(M^2-m₂))⁻¹*(k^2+w^2)⁻¹)
  have hden : 0 < x+m₂ := add_pos_of_pos_of_nonneg hx hm₂
  have hex :
      verifyCrossCovariance a M m₂ x = Real.exp (a*M)*Real.exp (-w*a)/(x+m₂) := by
    unfold verifyCrossCovariance
    rw [← Real.exp_add]
    congr 2
    change -a*(w-M) = a*M + -w*a
    ring
  have hp : ∃ L : ℝ, IntegrableOn F (Ioi 0) ∧
      (∫ k : ℝ in Ioi 0, F k) = (Real.pi/2)*(L-Real.exp (-w*a))/(x+m₂) ∧
      verifyCrossResidue a M m₂ = Real.exp (a*M)*L := by
    by_cases hbelow : m₂<M^2
    · let c := Real.sqrt (M^2-m₂)
      refine ⟨Real.exp (-c*a), ?_⟩
      have hn : M^2-m₂<w^2 := by rw [hw]; linarith
      obtain ⟨hi,he⟩ := verify_cross_pair_subthreshold ha hwpos hbelow hn
      have hd : w^2-(M^2-m₂)=x+m₂ := by rw [hw]; ring
      refine ⟨hi, ?_, ?_⟩
      · simpa only [hd, F] using he
      · rw [verifyCrossResidue, if_pos hbelow.le, ← Real.exp_add]
        congr 1
        change a*(M-c) = a*M+-c*a
        ring
    · let q := Real.sqrt (m₂-M^2)
      have hM : M^2≤m₂ := le_of_not_gt hbelow
      have hs : Real.sin (a*q)=0 := by
        rcases hadm with hm | hres
        · have hq : q=0 := by simp [q, le_antisymm hM hm]
          rw [hq,mul_zero,Real.sin_zero]
        · exact hres
      refine ⟨Real.cos (a*q), ?_⟩
      obtain ⟨hi,he⟩ := verify_cross_pair_resonant ha hwpos hM hs
      have hd : w^2+(m₂-M^2)=x+m₂ := by rw [hw]; ring
      refine ⟨hi, ?_, ?_⟩
      · simpa only [hd,F] using he
      · by_cases hle : m₂≤M^2
        · have heq := le_antisymm hle hM
          rw [verifyCrossResidue, if_pos hle]
          simp [q, heq]
        · exact if_neg hle
  obtain ⟨L,hi,hI,hres⟩ := hp
  have hAE : (fun s => verifyCrossContinuum a M m₂ s/(x+s)) =ᵐ[volume.restrict (Ioi (M^2))]
      fun s => crossDensity a M m₂ s/(x+s) := by
    filter_upwards [ae_restrict_of_ae (verifyCrossContinuum_ae a M m₂)] with s hs
    simp only [hs]
  constructor
  · apply Integrable.congr _ hAE.symm
    apply (verify_cross_spectral_integrable_iff _ _).2
    apply (hi.const_mul (-(2*Real.exp (a*M)/Real.pi))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with k hk
    exact (verify_cross_pair_point hk hw).symm
  · rw [integral_congr_ae hAE, resume_bulk_spectral_substitution (M^2)]
    have hsub :
      (∫ k : ℝ in Ioi 0, (2*k)*(crossDensity a M m₂ (k^2+M^2)/(x+(k^2+M^2)))) =
        -(2*Real.exp (a*M)/Real.pi)*(∫ k : ℝ in Ioi 0, F k) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi (fun k hk => verify_cross_pair_point hk hw)
    rw [hsub,hI,hres,hex]
    field_simp [Real.pi_ne_zero, hden.ne']
    ring

end UV.RevisionSpectrum
