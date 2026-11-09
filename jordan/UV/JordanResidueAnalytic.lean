import UV.MatrixPole
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Simple-pole numerators and regular parts on arbitrary analytic domains.
Neither the domain's geometry nor a residue/contour identity is assumed
here: the division and its removable value are derived pointwise. -/

noncomputable section
open Set Filter Complex
open scoped Topology

namespace UV

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]

omit [CompleteSpace Z] in
/-- Analyticity of the divided difference at and away from its center. -/
theorem analyticAt_dslope_of_analyticAt {G : ℂ → Z} {p z : ℂ}
    (hp : AnalyticAt ℂ G p) (hz : AnalyticAt ℂ G z) : AnalyticAt ℂ (dslope G p) z := by
  by_cases hzp : z = p
  · subst z
    obtain ⟨q,hq⟩ := hp
    exact ⟨q.fslope, hq.has_fpower_series_dslope_fslope⟩
  · have hq : AnalyticAt ℂ (fun w : ℂ => (w-p)⁻¹ • (G w-G p)) z :=
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzp)).smul
        (hz.sub analyticAt_const)
    apply hq.congr
    filter_upwards [eventually_ne_nhds hzp] with w hw
    simp only [dslope_of_ne G hw, slope, vsub_eq_sub]

omit [CompleteSpace Z] in
theorem analyticOnNhd_dslope {G : ℂ → Z} {U : Set ℂ} {p : ℂ}
    (hG : AnalyticOnNhd ℂ G U) (hp : p ∈ U) : AnalyticOnNhd ℂ (dslope G p) U :=
  fun z hz => analyticAt_dslope_of_analyticAt (hG p hp) (hG z hz)

/-- A unique simple scalar zero gives an actual holomorphic numerator and
an actual holomorphic regular part on the entire admitted domain. The
residue is the genuine punctured-limit coefficient. -/
theorem analytic_simple_denominator_regular_part {k : ℂ → ℂ} {n : ℂ → Z}
    {U : Set ℂ} {p : ℂ} (hp : p ∈ U)
    (hk : AnalyticOnNhd ℂ k U) (hn : AnalyticOnNhd ℂ n U)
    (hzero : k p = 0) (hderiv : deriv k p ≠ 0)
    (honly : ∀ z ∈ U, z ≠ p → k z ≠ 0) :
    let G := fun z => (dslope k p z)⁻¹ • n z
    AnalyticOnNhd ℂ G U ∧ AnalyticOnNhd ℂ (dslope G p) U ∧
      (∀ z ∈ U, z ≠ p → (k z)⁻¹ • n z = (z-p)⁻¹ • G z) ∧
      simplePoleResidue (fun z => (k z)⁻¹ • n z) p = G p := by
  let G : ℂ → Z := fun z => (dslope k p z)⁻¹ • n z
  have hd : AnalyticOnNhd ℂ (dslope k p) U := analyticOnNhd_dslope hk hp
  have hdne : ∀ z ∈ U, dslope k p z ≠ 0 := by
    intro z hz
    by_cases hzp : z = p
    · simpa only [hzp, dslope_same] using hderiv
    · rw [dslope_of_ne k hzp]
      simp only [slope, hzero, vsub_eq_sub, sub_zero, smul_eq_mul]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hzp)) (honly z hz hzp)
  have hG : AnalyticOnNhd ℂ G U := (hd.inv hdne).smul hn
  refine ⟨hG, analyticOnNhd_dslope hG hp, ?_, ?_⟩
  · intro z _ hzp
    dsimp only [G]
    rw [dslope_of_ne k hzp]
    simp only [slope, hzero, vsub_eq_sub, sub_zero, smul_eq_mul, smul_smul]
    congr 1
    field_simp [sub_ne_zero.mpr hzp]
  · obtain ⟨_, _, _, _, _, _, _, hres⟩ := local_simple_denominator_pole
      (hk p hp) (hn p hp) hzero (hk p hp).differentiableAt.hasDerivAt hderiv
    simpa only [G, dslope_same] using hres

end UV
