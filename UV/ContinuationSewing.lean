import UV.ContinuationSewingDifference

/-! The positive-band obstruction for complete Maxwell sewing on a fixed
Euclidean sector plane. The real variable in this file is squared Euclidean
momentum. No Lorentzian pole prescription or change of sector is used. -/

noncomputable section
open MeasureTheory Filter Set Polynomial
open scoped ENNReal Topology

namespace UV.ContinuationSewing

open UV.RevisionSpectrum (reciprocalDiff finite_difference_sewing_diverges)

def bandConstant (n : ℕ) (s₀ : ℝ) : ℝ :=
  ((n+1).factorial*s₀) / (((n:ℝ)+3)^(n+2))

theorem bandConstant_pos {s₀ : ℝ} (h : 0 < s₀) (n : ℕ) :
    0 < bandConstant n s₀ := by
  unfold bandConstant
  have hf : 0 < (((n+1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos (n+1)
  positivity

theorem differenceKernel_nonneg (n : ℕ) {s x h : ℝ} (hs : 0 ≤ s) (hx : 0 < x)
    (hh : 0 ≤ h) : 0 ≤ differenceKernel n s x h := by
  unfold differenceKernel
  positivity

theorem differenceKernel_band_lower (n : ℕ) {s₀ s x : ℝ} (hs₀ : 0 < s₀)
    (hs : s₀ ≤ s) (hsx : s ≤ x) : bandConstant n s₀ / x ≤ differenceKernel n s x x := by
  let P := ∏ j ∈ Finset.range (n+1+1), (s+x+(j:ℝ)*x)
  let B := (((n:ℝ)+3)*x)^(n+2)
  have hs' : 0 < s := hs₀.trans_le hs
  have hx : 0 < x := hs'.trans_le hsx
  have hB : 0 < B := by dsimp [B]; positivity
  have hP : 0 < P := by
    exact Finset.prod_pos (fun j _ => by positivity)
  have hPB : P ≤ B := by
    unfold P B
    calc
      _ ≤ ∏ _j ∈ Finset.range (n+1+1), ((n:ℝ)+3)*x := by
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro j hj
        have hj' : (j:ℝ) ≤ (n:ℝ)+1 := by
          exact_mod_cast (show j ≤ n+1 from Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        have hjx := mul_le_mul_of_nonneg_right hj' hx.le
        nlinarith
      _ = _ := by simp [Nat.add_assoc]
  have hEq : bandConstant n s₀ / x = ((n+1).factorial*s₀*x^(n+1))/B := by
    unfold bandConstant B
    rw [mul_pow, show n+2 = (n+1)+1 by omega, pow_succ x (n+1)]
    have hh : (n:ℝ)+3 ≠ 0 := by positivity
    field_simp [hx.ne', hh]
  have hNum : (n+1).factorial * s₀ * x^(n+1) ≤ (n+1).factorial * s * x^(n+1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity)
  rw [hEq, differenceKernel]
  change _ ≤ (((n+1).factorial : ℝ)*s*x^(n+1))/P
  exact (div_le_div_of_nonneg_left (by positivity) hP hPB).trans
    (div_le_div_of_nonneg_right hNum hP.le)

theorem differenceKernel_mass_lower (ρ : Measure ℝ) (n : ℕ) {s₀ s₁ x : ℝ}
    (hs₀ : 0 < s₀) (hx : 0 < x) (hxb : s₁ ≤ x)
    (hs : ∀ᵐ s ∂ρ, 0 ≤ s) (hfin : ρ (Icc s₀ s₁) ≠ ⊤)
    (hInt : Integrable (fun s => differenceKernel n s x x) ρ) :
    (bandConstant n s₀ * ρ.real (Icc s₀ s₁))/x ≤ ∫ s, differenceKernel n s x x ∂ρ := by
  let B := Icc s₀ s₁
  let c := bandConstant n s₀ / x
  have hi : Integrable (B.indicator fun _ => c) ρ :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const hfin)
  have h := integral_mono_ae hi hInt (by
    filter_upwards [hs] with s hsp
    by_cases hb : s ∈ B
    · rw [indicator_of_mem hb]
      exact differenceKernel_band_lower n hs₀ hb.1 (hb.2.trans hxb)
    · rw [indicator_of_notMem hb]
      exact differenceKernel_nonneg n hsp hx hx.le)
  rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul] at h
  change ρ.real (Icc s₀ s₁) * (bandConstant n s₀/x) ≤ _ at h
  convert h using 1; ring

/-- Complete response including one overall sign, an arbitrary contact
polynomial, and mass-dependent polynomial subtractions. -/
def contactSubtractedResponse (ρ : Measure ℝ) (P : Polynomial ℝ)
    (g : ℝ → Polynomial ℝ) (sign x : ℝ) : ℝ :=
  sign * (P.eval x + ∫ s, x/(s+x) - (g s).eval x ∂ρ)

theorem difference_contactSubtractedResponse (ρ : Measure ℝ) (P : Polynomial ℝ)
    (g : ℝ → Polynomial ℝ) (sign : ℝ) {h R : ℝ} (hR : 0 < R) (hh : 0 ≤ h) (n : ℕ)
    (hP : P.natDegree < n+1) (hs : ∀ᵐ s ∂ρ, 0 ≤ s)
    (hg : ∀ᵐ s ∂ρ, (g s).natDegree < n+1)
    (hf : ∀ x ≥ R, Integrable (fun s => x/(s+x) - (g s).eval x) ρ)
    (x : ℝ) (hx : R ≤ x) :
    Integrable (fun s => differenceKernel n s x h) ρ ∧
      |reciprocalDiff h (n+1) (contactSubtractedResponse ρ P g sign) x| =
        |sign| * ∫ s, differenceKernel n s x h ∂ρ := by
  obtain ⟨hi, heq⟩ := difference_subtracted_integral ρ g hR hh n hs hg hf x hx
  refine ⟨hi, ?_⟩
  unfold contactSubtractedResponse
  rw [reciprocalDiff_mul, reciprocalDiff_add, reciprocalDiff_polynomial P h x hP,
    zero_add, heq, abs_mul, abs_neg]
  have hnonneg : 0 ≤ ∫ s, differenceKernel n s x h ∂ρ := by
    apply integral_nonneg_of_ae
    filter_upwards [hs] with s hsp
    exact differenceKernel_nonneg n hsp (hR.trans_le hx) hh
  rw [abs_of_nonneg hnonneg]

/-- Finite contacts and polynomial dispersion subtractions cannot make the
same measured current integrable against a photon with a Maxwell tail. -/
theorem contactSubtracted_radial_sewing_diverges (ρ : Measure ℝ) (P : Polynomial ℝ)
    (g : ℝ → Polynomial ℝ) (D : ℝ → ℝ) (sign : ℝ) (hSign : sign ≠ 0) (n : ℕ)
    {R c s₀ s₁ : ℝ} (hR : 0 < R) (hc : 0 < c) (hs₀ : 0 < s₀) (hxb : s₁ ≤ R)
    (hfin : ρ (Icc s₀ s₁) ≠ ⊤) (hpos : ρ (Icc s₀ s₁) ≠ 0)
    (hP : P.natDegree < n+1) (hs : ∀ᵐ s ∂ρ, 0 ≤ s)
    (hg : ∀ᵐ s ∂ρ, (g s).natDegree < n+1)
    (hf : ∀ x ≥ R, Integrable (fun s => x/(s+x) - (g s).eval x) ρ)
    (hK : AEStronglyMeasurable (contactSubtractedResponse ρ P g sign) (volume.restrict (Ioi R)))
    (hD : ∀ x > R, c/x ≤ D x) :
    ¬ IntegrableOn (fun x => x * D x * contactSubtractedResponse ρ P g sign x) (Ioi R) := by
  let d := |sign| * bandConstant n s₀ * ρ.real (Icc s₀ s₁)
  have hmass : 0 < ρ.real (Icc s₀ s₁) := ENNReal.toReal_pos hpos hfin
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos (mul_pos (abs_pos.mpr hSign) (bandConstant_pos hs₀ n)) hmass
  apply finite_difference_sewing_diverges hc hd hR hK hD (n+1)
  intro x hx
  have hx' : 0 < x := hR.trans hx
  obtain ⟨hi, heq⟩ := difference_contactSubtractedResponse ρ P g sign hR hx'.le n hP hs hg hf x hx.le
  rw [heq]
  have h := differenceKernel_mass_lower ρ n hs₀ hx' (hxb.trans hx.le) hs hfin hi
  convert mul_le_mul_of_nonneg_left h (abs_nonneg sign) using 1; dsimp [d]; ring

/-- Exact transfer of radial tail nonintegrability to the four-dimensional
Euclidean momentum space. The positive factors from the radial Jacobian
are retained. -/
theorem fourMomentum_sewing_diverges_of_radial (D K : ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (h : ¬ IntegrableOn (fun X => X * D X * K X) (Ioi R)) :
    ¬ IntegrableOn (fun q : ScalarMomentum => D (‖q‖^2)*K (‖q‖^2))
      {q | R < ‖q‖^2} := by
  intro hq
  let f := fun r : ℝ => if R < r^2 then D (r^2)*K (r^2) else 0
  have hqmeas : MeasurableSet {q : ScalarMomentum | R < ‖q‖^2} :=
    measurableSet_lt measurable_const (measurable_norm.pow_const _)
  have hfi := (integrable_indicator_iff hqmeas).mpr hq
  have hf : Integrable (fun q : ScalarMomentum => f ‖q‖) := by
    simpa only [f, indicator, mem_setOf_eq] using hfi
  have hr := (integrable_fun_norm_addHaar (E := ScalarMomentum) volume (f := f)).mp hf
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul] at hr
  let S := Ioi (Real.sqrt R)
  let g := fun X : ℝ => X*D X*K X
  have hS : S ⊆ Ioi 0 := Ioi_subset_Ioi (Real.sqrt_nonneg _)
  have hradR : IntegrableOn (fun r : ℝ => r^3 * f r) S := hr.mono_set hS
  have hrad2 : IntegrableOn (fun r : ℝ => 2 * (r^3 * f r)) S := hradR.const_mul 2
  have hi : IntegrableOn (fun r : ℝ => |2*r| • g (r^2)) S := by
    refine hrad2.congr_fun ?_ (show MeasurableSet S from measurableSet_Ioi)
    intro r hr
    have hr₁ : Real.sqrt R < r := hr
    have hr₀ : 0 < r := (Real.sqrt_nonneg R).trans_lt hr₁
    have hrr : R < r^2 := by
      rw [← Real.sq_sqrt hR.le]
      exact (sq_lt_sq₀ (Real.sqrt_nonneg R) hr₀.le).mpr hr₁
    simp only [f, g, smul_eq_mul, if_pos hrr, abs_of_pos (show 0 < 2*r by positivity)]
    ring
  have hder : ∀ r ∈ S, HasDerivWithinAt (fun r : ℝ => r^2) (2*r) S r := by
    intro r _
    simpa using ((hasDerivAt_id r).pow 2).hasDerivWithinAt
  have hinj : InjOn (fun r : ℝ => r^2) S := by
    apply StrictMonoOn.injOn
    intro r hr t ht hrt
    exact (sq_lt_sq₀ (hS hr).le (hS ht).le).mpr hrt
  have himage : (fun r : ℝ => r^2) '' S = Ioi R := by
    ext X
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hrt : Real.sqrt R < r := hr
      change R < r^2
      rw [← Real.sq_sqrt hR.le]
      exact (sq_lt_sq₀ (Real.sqrt_nonneg R) (hS hr).le).mpr hrt
    · intro hX
      change R < X at hX
      have hXp := hR.trans hX
      exact ⟨Real.sqrt X, Real.sqrt_lt_sqrt hR.le hX, Real.sq_sqrt hXp.le⟩
  have hj := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    (show MeasurableSet S from measurableSet_Ioi) hder hinj g).mpr hi
  rw [himage] at hj
  exact h hj

/-- Positive spectral band obstruction for the actual four-momentum
contraction, with all finite polynomial contacts and subtractions included
in the same transverse kernel. The sector parameter selects the fixed
plane in which both the photon and current are evaluated. -/
theorem contactSubtracted_Maxwell_sewing_diverges {Sector : Type*} (plane : Sector)
    (ρ : Sector → Measure ℝ) (P : Sector → Polynomial ℝ)
    (g : Sector → ℝ → Polynomial ℝ) (D : Sector → ℝ → ℝ)
    (sign : ℝ) (hSign : sign ≠ 0) (n : ℕ)
    {R c s₀ s₁ : ℝ} (hR : 0 < R) (hc : 0 < c) (hs₀ : 0 < s₀) (hxb : s₁ ≤ R)
    (hfin : ρ plane (Icc s₀ s₁) ≠ ⊤) (hpos : ρ plane (Icc s₀ s₁) ≠ 0)
    (hP : (P plane).natDegree < n+1) (hs : ∀ᵐ s ∂ρ plane, 0 ≤ s)
    (hg : ∀ᵐ s ∂ρ plane, (g plane s).natDegree < n+1)
    (hf : ∀ x ≥ R, Integrable (fun s => x/(s+x) - (g plane s).eval x) (ρ plane))
    (hK : AEStronglyMeasurable (contactSubtractedResponse (ρ plane) (P plane) (g plane) sign)
      (volume.restrict (Ioi R)))
    (hD : ∀ x > R, c/x ≤ D plane x) :
    ¬ IntegrableOn (fun q : ScalarMomentum => D plane (‖q‖^2) *
      contactSubtractedResponse (ρ plane) (P plane) (g plane) sign (‖q‖^2))
      {q | R < ‖q‖^2} := by
  apply fourMomentum_sewing_diverges_of_radial _ _ hR
  exact contactSubtracted_radial_sewing_diverges (ρ plane) (P plane) (g plane) (D plane) sign
    hSign n hR hc hs₀ hxb hfin hpos hP hs hg hf hK hD

end UV.ContinuationSewing
