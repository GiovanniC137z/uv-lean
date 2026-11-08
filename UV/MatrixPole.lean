import UV.PoleCertificates
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Actual finite-matrix inverse and observable simple-pole coefficients.
Local pole numerators are constructed from the determinant's divided
slope and the analytic adjugate, rather than supplied as residue data. -/

noncomputable section
open Complex Filter Set Metric
open scoped Topology

namespace UV

/-- A nonzero scalar derivative constructs a disk with no other denominator
zero; analyticity constructs the holomorphic numerator on that same disk. -/
theorem local_simple_denominator_pole {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℂ Z] [CompleteSpace Z] {k : ℂ → ℂ} {n : ℂ → Z} {p d : ℂ}
    (hk : AnalyticAt ℂ k p) (hn : AnalyticAt ℂ n p)
    (hkzero : k p=0) (hd : HasDerivAt k d p) (hdne : d≠0) :
    ∃ r : ℝ, 0<r ∧
      DifferentiableOn ℂ k (closedBall p r) ∧
      DifferentiableOn ℂ n (closedBall p r) ∧
      (∀ z ∈ closedBall p r, z≠p → k z≠0) ∧
      DifferentiableOn ℂ (fun z => (dslope k p z)⁻¹ • n z) (closedBall p r) ∧
      (∀ z ∈ closedBall p r, z≠p →
        (k z)⁻¹ • n z = (z-p)⁻¹ • ((dslope k p z)⁻¹ • n z)) ∧
      simplePoleResidue (fun z => (k z)⁻¹ • n z) p = d⁻¹ • n p := by
  have hOnly : ∀ᶠ z in 𝓝 p, z≠p → k z≠0 := by
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (eventually_nhdsWithin_iff.mp (hd.eventually_ne hdne : ∀ᶠ z in 𝓝[≠] p, k z≠0))
  have hke : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ k z := (isOpen_analyticAt ℂ k).mem_nhds hk
  have hne : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ n z := (isOpen_analyticAt ℂ n).mem_nhds hn
  obtain ⟨R,hR,hball⟩ := Metric.eventually_nhds_iff.mp (hke.and (hne.and hOnly))
  have hhalf : 0<R/2 := by positivity
  have hdata (z : ℂ) (hz : z∈closedBall p (R/2)) :=
    hball (lt_of_le_of_lt hz (by linarith : R/2<R))
  have hkD : DifferentiableOn ℂ k (closedBall p (R/2)) :=
    fun z hz => (hdata z hz).1.differentiableAt.differentiableWithinAt
  have hnD : DifferentiableOn ℂ n (closedBall p (R/2)) :=
    fun z hz => (hdata z hz).2.1.differentiableAt.differentiableWithinAt
  have hOnlyD : ∀ z∈closedBall p (R/2), z≠p → k z≠0 :=
    fun z hz => (hdata z hz).2.2
  have hdp : deriv k p≠0 := by rw [hd.deriv]; exact hdne
  have hp : p∈ball p (R/2) := mem_ball_self hhalf
  obtain ⟨hG,hf⟩ := simple_denominator_pole_numerator hp hkD hnD hkzero hdp hOnlyD
  refine ⟨R/2,hhalf,hkD,hnD,hOnlyD,hG,hf,?_⟩
  simpa only [hd.deriv] using simple_denominator_residue hp hkD hnD hkzero hdp hOnlyD

end UV
