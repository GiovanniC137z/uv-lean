import UV.VerifySpectrumAtom
import UV.VerifySpectrumCrossStieltjes
import UV.ExtendStablePole
import UV.EvenDescent
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Necessity of the embedded-pole resonance from the real atom extracted
by the ordinary Stieltjes transform. Analytic agreement is obtained from
the positive-Euclidean slice by the identity theorem. -/

noncomputable section
open MeasureTheory Filter Set UV.SectorPlane
open scoped Topology

namespace UV.RevisionSpectrum

def verifyCrossComplex (a M m₂ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((a:ℂ)*((M:ℂ)-principalSqrt (z+((M^2:ℝ):ℂ))))/(z+(m₂:ℂ))

theorem verify_cross_complex_analyticOnNhd (a M : ℝ) {m₂ : ℝ} (hm₂ : 0≤m₂) :
    AnalyticOnNhd ℂ (verifyCrossComplex a M m₂) verifyUpperStieltjesDomain := by
  intro z hz
  have hs := verify_upper_stieltjes_add_nonnegative hz (sq_nonneg M)
  have hd := verify_upper_stieltjes_add_nonnegative hz hm₂
  unfold verifyCrossComplex
  have hshift : AnalyticAt ℂ (fun w : ℂ => w+((M^2:ℝ):ℂ)) z :=
    analyticAt_id.add analyticAt_const
  have hs' := (principalSqrt_analyticOnNhd_slitPlane _ hs).comp'
    (f := fun w : ℂ => w+((M^2:ℝ):ℂ)) hshift
  have hnum : AnalyticAt ℂ (fun w : ℂ => (a:ℂ)*((M:ℂ)-principalSqrt (w+((M^2:ℝ):ℂ)))) z :=
    analyticAt_const.mul (analyticAt_const.sub hs')
  have hden : AnalyticAt ℂ (fun w : ℂ => w+(m₂:ℂ)) z := analyticAt_id.add analyticAt_const
  exact hnum.cexp'.div hden (Complex.slitPlane_ne_zero hd)

theorem verify_cross_complex_ofReal {a M m₂ x : ℝ} (hx : 0<x) :
    verifyCrossComplex a M m₂ (x:ℂ) = (verifyCrossCovariance a M m₂ x : ℂ) := by
  have h : 0≤x+M^2 := by positivity
  rw [verifyCrossComplex, verifyCrossCovariance, ← Complex.ofReal_add, principalSqrt_ofReal h]
  push_cast
  have he : (a:ℂ)*((M:ℂ)-(Real.sqrt (x+M^2):ℂ)) =
      -(a:ℂ)*((Real.sqrt (x+M^2):ℂ)-(M:ℂ)) := by ring
  rw [he]

theorem verify_cross_complex_vertical {a M m₂ h : ℝ} (hh : 0<h) :
    verifyCrossComplex a M m₂ (verifyStieltjesVertical m₂ h) = crossUpper a M m₂ m₂ h := by
  have he : verifyStieltjesVertical m₂ h + ((M^2:ℝ):ℂ) =
      ((M^2-m₂:ℝ):ℂ)+(h:ℂ)*Complex.I := by
    unfold verifyStieltjesVertical
    push_cast
    ring
  have hd : verifyStieltjesVertical m₂ h + (m₂:ℂ) =
      ((m₂-m₂:ℝ):ℂ)+(h:ℂ)*Complex.I := by
    unfold verifyStieltjesVertical
    push_cast
    ring
  rw [verifyCrossComplex, crossUpper, he, hd, principalSqrt_upper_eq _ hh]

private theorem verify_real_axis_frequently_eq {F G : ℂ → ℂ}
    (h : ∀ x : ℝ, 0<x → F (x:ℂ) = G (x:ℂ)) :
    ∃ᶠ z in 𝓝[≠] (1:ℂ), F z = G z := by
  have ht : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] (1:ℝ)) (𝓝[≠] (1:ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa only [Complex.ofReal_one] using
        (Complex.continuous_ofReal.continuousAt (x := (1:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : 1<x := hx
      have hne : (x:ℂ)≠(1:ℂ) := by
        intro hξ
        exact hx'.ne' (Complex.ofReal_inj.mp (hξ.trans Complex.ofReal_one.symm))
      exact hne
  apply ht.frequently
  apply Eventually.frequently
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact h x (zero_lt_one.trans (mem_Ioi.mp hx))

theorem verify_cross_signed_continuation {νpos νneg : Measure ℝ}
    (a M : ℝ) {m₂ y : ℝ} (hm₂ : 0≤m₂) (hy : 0<y)
    (hspos : ∀ᵐ s ∂νpos,0≤s) (hsneg : ∀ᵐ s ∂νneg,0≤s)
    (hipos : Integrable (stieltjesWeight y) νpos) (hineg : Integrable (stieltjesWeight y) νneg)
    (he : ∀ x : ℝ, 0<x → diagonalStieltjes νpos x-diagonalStieltjes νneg x =
      verifyCrossCovariance a M m₂ x) :
    EqOn (fun z => verifyComplexStieltjes νpos z-verifyComplexStieltjes νneg z)
      (verifyCrossComplex a M m₂) verifyUpperStieltjesDomain := by
  have hA := (verify_complex_stieltjes_analyticOnNhd hy hspos hipos).sub
    (verify_complex_stieltjes_analyticOnNhd hy hsneg hineg)
  apply hA.eqOn_of_preconnected_of_frequently_eq
    (verify_cross_complex_analyticOnNhd a M hm₂) verify_upper_stieltjes_preconnected
    (z₀ := 1) (Or.inl (by simp))
  apply verify_real_axis_frequently_eq
  intro x hx
  change verifyComplexStieltjes νpos (x:ℂ)-verifyComplexStieltjes νneg (x:ℂ) =
    verifyCrossComplex a M m₂ (x:ℂ)
  rw [verify_complex_stieltjes_ofReal, verify_complex_stieltjes_ofReal, ← Complex.ofReal_sub,
    he x hx, verify_cross_complex_ofReal hx]

theorem verify_cross_signed_residue {νpos νneg : Measure ℝ}
    (a M : ℝ) {m₂ y : ℝ} (hm₂ : 0≤m₂) (hy : 0<y)
    (hspos : ∀ᵐ s ∂νpos,0≤s) (hsneg : ∀ᵐ s ∂νneg,0≤s)
    (hipos : Integrable (stieltjesWeight y) νpos) (hineg : Integrable (stieltjesWeight y) νneg)
    (he : ∀ x : ℝ, 0<x → diagonalStieltjes νpos x-diagonalStieltjes νneg x =
      verifyCrossCovariance a M m₂ x) :
    ((νpos.real ({m₂}:Set ℝ)-νneg.real ({m₂}:Set ℝ):ℝ):ℂ) =
      Complex.exp ((a:ℂ)*((M:ℂ)-spectralRootUpper (M^2-m₂) 0)) := by
  have hC := verify_cross_signed_continuation a M hm₂ hy hspos hsneg hipos hineg he
  have hL := (verify_stieltjes_extracts_real_atom hm₂ hy hspos hipos).sub
    (verify_stieltjes_extracts_real_atom hm₂ hy hsneg hineg)
  rw [← Complex.ofReal_sub] at hL
  apply tendsto_nhds_unique _ (crossUpper_pole_limit a M m₂)
  apply hL.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : 0<h := hh
  change ((h:ℂ)*Complex.I)*verifyComplexStieltjes νpos (verifyStieltjesVertical m₂ h) -
      ((h:ℂ)*Complex.I)*verifyComplexStieltjes νneg (verifyStieltjesVertical m₂ h) =
    ((h:ℂ)*Complex.I)*crossUpper a M m₂ m₂ h
  have heq := hC (x := verifyStieltjesVertical m₂ h) (verify_stieltjes_vertical_mem hh')
  dsimp only at heq
  rw [← mul_sub, heq, verify_cross_complex_vertical hh']

/-- No ordinary reference-integrable signed spectral law realizes a generic
embedded pole. The signed atom also has the source's precise residue. -/
theorem verify_cross_signed_necessity_and_atom {νpos νneg : Measure ℝ}
    (a M : ℝ) {m₂ y : ℝ} (hm₂ : 0≤m₂) (hy : 0<y)
    (hspos : ∀ᵐ s ∂νpos,0≤s) (hsneg : ∀ᵐ s ∂νneg,0≤s)
    (hipos : Integrable (stieltjesWeight y) νpos) (hineg : Integrable (stieltjesWeight y) νneg)
    (he : ∀ x : ℝ, 0<x → diagonalStieltjes νpos x-diagonalStieltjes νneg x =
      verifyCrossCovariance a M m₂ x) :
    (m₂≤M^2 ∨ Real.sin (a*Real.sqrt (m₂-M^2))=0) ∧
    νpos.real ({m₂}:Set ℝ)-νneg.real ({m₂}:Set ℝ) = verifyCrossResidue a M m₂ := by
  have hR := verify_cross_signed_residue a M hm₂ hy hspos hsneg hipos hineg he
  by_cases hm : m₂≤M^2
  · refine ⟨Or.inl hm, ?_⟩
    rw [crossPoleCoeff_below hm] at hR
    rw [verifyCrossResidue, if_pos hm]
    exact Complex.ofReal_inj.mp hR
  · have hm' := lt_of_not_ge hm
    have h := crossPoleCoeff_above (a:=a) hm'
    dsimp only at h
    rw [← hR] at h
    simp only [Complex.ofReal_re, Complex.ofReal_im] at h
    have hz : Real.exp (a*M)*Real.sin (a*Real.sqrt (m₂-M^2))=0 := by linarith [h.2]
    exact ⟨Or.inr ((mul_eq_zero.mp hz).resolve_left (Real.exp_pos _).ne'),
      by simpa only [verifyCrossResidue, if_neg hm] using h.1⟩

end UV.RevisionSpectrum
