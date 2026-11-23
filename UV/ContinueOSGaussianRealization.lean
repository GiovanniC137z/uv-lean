import UV.ContinueOSGaussianWick
import UV.ContinueOSGaussianModification
import UV.VerifyCurvaturePairings
import UV.ContinueOSWickRealization

/-! The full free massive Gaussian realization for the boundary and
positive-depth point probes of the two weak-coupling reflection tests. -/

noncomputable section
open MeasureTheory Matrix Set Filter
open scoped Matrix Topology

namespace UV

private theorem osMonomial_coordinate_measurable {ι : Type*} (l : List ι) :
    Measurable (osMonomial (fun (i : ι) (z : ι → ℝ) => z i) l) := by
  induction l with
  | nil => exact measurable_const
  | cons i l ih => exact (measurable_pi_apply i).mul ih

theorem osQuarticFiniteLaw_wick {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (s : ι → OSQuarticSlot) :
    OSWickMoments (osQuarticFiniteLaw hm hr s) (fun (i : ι) (z : ι → ℝ) => z i)
      (fun i j => osQuarticCovariance m r (s i) (s j)) := by
  let D : Matrix ι ι ℝ := fun i j => osQuarticCovariance m r (s i) (s j)
  let hD := osQuarticCovariance_posSemidef hm hr s
  let d := hD.1.eigenvalues
  let U : Matrix ι ι ℝ := hD.1.eigenvectorUnitary
  have hw := MarkedPhoton.osLinearGaussian_wick d hD.eigenvalues_nonneg U
  have hcov (i j : ι) : (∑ k, U i k*d k*U j k) = D i j := by
    have he : D = U*Matrix.diagonal d*star U := hD.1.spectral_theorem
    rw [he,Matrix.mul_apply]
    simp only [Matrix.mul_diagonal,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial]
  have hmean (l : List ι) : (∫ z, osMonomial (fun (i : ι) (z : ι → ℝ) => z i) l z ∂osQuarticFiniteLaw hm hr s) =
      ∫ z, osMonomial (fun b z => ∑ i, U b i*z i) l z ∂MarkedPhoton.coordinateLaw d :=
    integral_map (by fun_prop : AEMeasurable U.mulVec (MarkedPhoton.coordinateLaw d))
      (osMonomial_coordinate_measurable l).aestronglyMeasurable
  constructor
  · intro l
    apply (integrable_map_measure (osMonomial_coordinate_measurable l).aestronglyMeasurable
      (by fun_prop : AEMeasurable U.mulVec (MarkedPhoton.coordinateLaw d))).mpr
    exact hw.integrable l
  · intro n l hl
    rw [hmean,hw.moment n l hl]
    congr 1
    exact funext₂ hcov

private theorem osQuarticProcess_wick {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    (μ : Measure (OSQuarticSlot → ℝ)) (hμ : IsProjectiveLimit (α := fun _ => ℝ) μ (osGaussianFamily hm hr)) :
    OSWickMoments μ (fun i z => z i) (osQuarticCovariance m r) := by
  classical
  have hlist (l : List OSQuarticSlot) (n : ℕ) (hn : l.length ≤ 2*n) :
      Integrable (osMonomial (fun (i : OSQuarticSlot) (z : OSQuarticSlot → ℝ) => z i) l) μ ∧
        (∫ z, osMonomial (fun (i : OSQuarticSlot) (z : OSQuarticSlot → ℝ) => z i) l z ∂μ) =
          osWickMoment (osQuarticCovariance m r) n l := by
    let J := l.toFinset
    let l' : List J := l.attach.map fun j => ⟨j.1,List.mem_toFinset.mpr j.2⟩
    have hl : l'.map Subtype.val = l := by
      simpa only [l',List.map_map,Function.comp_def] using List.attach_map_subtype_val l
    let E := osMonomial (fun (i : J) (z : J → ℝ) => z i) l'
    have hE : Measurable E := osMonomial_coordinate_measurable _
    have heq : osMonomial (fun (i : OSQuarticSlot) (z : OSQuarticSlot → ℝ) => z i) l = E ∘ J.restrict := by
      rw [←hl]
      funext z
      simp [E,osMonomial,List.map_map,Function.comp_def,Finset.restrict_def]
    have hfin := osQuarticFiniteLaw_wick hm hr (@Subtype.val _ (· ∈ J))
    have hp : μ.map J.restrict = osQuarticFiniteLaw hm hr (@Subtype.val _ (· ∈ J)) :=
      osQuarticGaussianProcess_projection hm hr μ hμ (@Subtype.val _ (· ∈ J))
    have hi : Integrable E (μ.map J.restrict) := by
      rw [hp]
      exact hfin.integrable _
    rw [heq]
    refine ⟨hi.comp_aemeasurable (Finset.measurable_restrict J).aemeasurable,?_⟩
    have hInt : (∫ z, (E ∘ J.restrict) z ∂μ) = ∫ z, E z ∂μ.map J.restrict :=
      (integral_map (Finset.measurable_restrict J).aemeasurable hE.aestronglyMeasurable).symm
    rw [hInt,hp]
    have hlen : l'.length ≤ 2*n := by simpa [l'] using hn
    rw [show (∫ z, E z ∂osQuarticFiniteLaw hm hr (@Subtype.val _ (· ∈ J))) = _ from hfin.moment n l' hlen]
    simpa [hl] using VerifyCurvaturePairings.osWickMoment_scaled (osQuarticCovariance m r)
      (@Subtype.val _ (· ∈ J)) (fun _ => 1) n l'
  exact ⟨fun l => (hlist l l.length (by omega)).1,fun n l hl => (hlist l n hl).2⟩

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
