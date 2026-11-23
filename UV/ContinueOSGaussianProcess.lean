import UV.ContinueOSGaussianExtension

/-! Extension of the fixed-depth compatible Gaussian distributions to the
cylinder sigma algebra on all boundary probes and all Euclidean points. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Finset Set
open scoped ENNReal Topology

namespace UV

abbrev osGaussianFamily {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (J : Finset OSQuarticSlot) :=
  @osQuarticFiniteLaw J _ (Classical.decEq _) _ _ hm hr Subtype.val

/-- Positive covariance kernel of the joint massive fixed-depth probes. -/
def osQuarticPositiveKernel {m r : ℝ} (hm : 0 < m) (hr : 0 < r) : OSPositiveCovariance OSQuarticSlot where
  entry := osQuarticCovariance m r
  pos := osQuarticCovariance_posSemidef hm hr

/-- Unique cylinder law on every boundary and transferred point probe. -/
theorem osQuarticGaussianProcess {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    ∃! μ : Measure (OSQuarticSlot → ℝ), IsProjectiveLimit (α := fun _ => ℝ) μ (osGaussianFamily hm hr) := by
  letI : Inhabited OSQuarticSlot := ⟨.inl .bump⟩
  exact osPositiveGaussianProcess (osQuarticPositiveKernel hm hr)

/-- A finite observable list can repeat coordinates in any order on the
common sample space. -/
theorem osQuarticGaussianProcess_projection {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    (μ : Measure (OSQuarticSlot → ℝ)) (hμ : IsProjectiveLimit (α := fun _ => ℝ) μ (osGaussianFamily hm hr))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → OSQuarticSlot) :
    μ.map (fun x => x ∘ s) = osQuarticFiniteLaw hm hr s := by
  classical
  let U := Finset.univ.image s
  let l (i : ι) : U := ⟨s i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have me : Measurable (fun (x : U → ℝ) => x ∘ l) := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  calc
    _ = (μ.map U.restrict).map (fun x => x ∘ l) := (Measure.map_map me (Finset.measurable_restrict U)).symm
    _ = _ := by
      rw [hμ]
      exact @osQuarticFiniteLaw_map U ι _ _ (Classical.decEq _) _ _ _ hm hr Subtype.val l

end UV
