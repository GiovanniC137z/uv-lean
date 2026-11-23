import UV.ContinueOSGaussianWick
import UV.ContinueOSGaussianModification
import UV.ContinueOSPositiveWick
import UV.ContinueOSWickRealization

/-! The full free massive Gaussian realization for the boundary and
positive-depth point probes of the two weak-coupling reflection tests. -/

noncomputable section
open MeasureTheory Matrix Set Filter
open scoped Matrix Topology

namespace UV

theorem osQuarticFiniteLaw_wick {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (s : ι → OSQuarticSlot) :
    OSWickMoments (osQuarticFiniteLaw hm hr s) (fun (i : ι) (z : ι → ℝ) => z i)
      (fun i j => osQuarticCovariance m r (s i) (s j)) :=
  osMatrixGaussian_wick _ _

private theorem osQuarticProcess_wick {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    (μ : Measure (OSQuarticSlot → ℝ)) (hμ : IsProjectiveLimit (α := fun _ => ℝ) μ (osGaussianFamily hm hr)) :
    OSWickMoments μ (fun i z => z i) (osQuarticCovariance m r) :=
  osPositiveProcess_wick (osQuarticPositiveKernel hm hr) μ hμ

/-- The ordinary massive Gaussian and its spatially measurable transferred
field satisfy the full Wick recurrence jointly with the boundary test probes. -/
theorem osQuarticGaussian_realization {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    ∃ (μ : Measure (OSQuarticSlot → ℝ)) (F : OSQuarticSlot → (OSQuarticSlot → ℝ) → ℝ),
      IsProbabilityMeasure μ ∧ OSWickMoments μ F (osQuarticCovariance m r) ∧
      Measurable (fun p : OSFourSpace × (OSQuarticSlot → ℝ) => F (.inr p.1) p.2) := by
  obtain ⟨μ,hμ,_⟩ := osQuarticGaussianProcess hm hr
  obtain ⟨Z,hZ,hmod⟩ := osQuarticGaussian_joint_modification hm hr μ hμ
  let F : OSQuarticSlot → (OSQuarticSlot → ℝ) → ℝ := Sum.elim (fun i z => z (.inl i)) Z
  have heq (i : OSQuarticSlot) : F i =ᵐ[μ] (fun z => z i) := by
    cases i with
    | inl i => exact EventuallyEq.rfl
    | inr x => exact hmod x
  have he (l : List OSQuarticSlot) : osMonomial F l =ᵐ[μ] osMonomial (fun i z => z i) l := by
    induction l with
    | nil => exact EventuallyEq.rfl
    | cons i l ih => exact (heq i).mul ih
  let hw := osQuarticProcess_wick hm hr μ hμ
  haveI (I : Finset OSQuarticSlot) : IsProbabilityMeasure (osGaussianFamily hm hr I) :=
    @osQuarticFiniteLaw_probability I _ (Classical.decEq _) _ _ hm hr Subtype.val
  exact ⟨μ,F,hμ.isProbabilityMeasure,⟨fun l => (hw.integrable l).congr (he l).symm,
    fun n l h => (integral_congr_ae (he l)).trans (hw.moment n l h)⟩,hZ⟩

/-- The raw boundary witness has the calculated negative right slope
under the actual constructed Gaussian measure, for each positive mass and
depth and each nonzero nonnegative compact switch. -/
theorem osRawQuartic_fixed_depth {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    {ζ : OSFourSpace → ℝ} (hc : Continuous ζ) (hk : HasCompactSupport ζ)
    (hn : 0 ≤ ζ) (hz : ∃ x, 0 < ζ x) :
    ∃ (μ : Measure (OSQuarticSlot → ℝ)) (F : OSQuarticSlot → (OSQuarticSlot → ℝ) → ℝ),
      IsProbabilityMeasure μ ∧ OSWickMoments μ F (osQuarticCovariance m r) ∧
      let A := fun ω => F (.inl .reflectedLocal) ω * F (.inl .localProbe) ω
      let V := osSpatialPotential volume (fun x ω => ζ x * F (.inr x) ω^4/24)
      HasDerivWithinAt (osGibbsExpectation μ V A) (osRawQuarticSlope m r ζ) (Ioi 0) 0 ∧
      ∀ᶠ g : ℝ in 𝓝[Ioi 0] 0, osGibbsExpectation μ V A g < 0 := by
  obtain ⟨μ,F,hμ,hW,hZ⟩ := osQuarticGaussian_realization hm hr
  exact ⟨μ,F,hμ,hW,osRawQuartic_realization hm hr hc hk hn hz F hW hZ⟩

end UV
