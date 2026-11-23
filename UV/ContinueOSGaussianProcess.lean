import UV.ContinueOSGaussianCountable

/-! Extension of the fixed-depth compatible Gaussian distributions to the
cylinder sigma algebra on all boundary probes and all Euclidean points. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Finset Set
open scoped ENNReal Topology

namespace UV

abbrev osGaussianFamily {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (J : Finset OSQuarticSlot) :=
  @osQuarticFiniteLaw J _ (Classical.decEq _) _ _ hm hr Subtype.val

private theorem osCountableProjection {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (s : ℕ → OSQuarticSlot)
    (μ : Measure (ℕ → ℝ)) (hμ : IsProjectiveLimit (α := fun _ => ℝ) μ (fun J =>
      osQuarticFiniteLaw hm hr (fun j : J => s j))) {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℕ) :
    μ.map (fun x => x ∘ f) = osQuarticFiniteLaw hm hr (s ∘ f) := by
  let U := Finset.univ.image f
  let l (i : ι) : U := ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have me : Measurable (fun (x : U → ℝ) => x ∘ l) := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  calc
    _ = (μ.map U.restrict).map (fun x => x ∘ l) := (Measure.map_map me (Finset.measurable_restrict U)).symm
    _ = _ := by rw [hμ]; exact osQuarticFiniteLaw_map hm hr (fun j : U => s j) l

private theorem osGaussianCountableCylinderLaw {m r : ℝ} (hm : 0 < m) (hr : 0 < r)
    (U : Set OSQuarticSlot) (hU : U.Countable) :
    ∃ μ : Measure (OSQuarticSlot → ℝ), IsProbabilityMeasure μ ∧
      ∀ (I : Finset OSQuarticSlot), (I : Set OSQuarticSlot) ⊆ U →
        μ.map I.restrict = osGaussianFamily hm hr I := by
  classical
  letI : Countable U := hU
  obtain ⟨e,he⟩ := Countable.exists_injective_nat U
  let f : OSQuarticSlot → ℕ := Function.extend Subtype.val e (fun _ => 0)
  let s : ℕ → OSQuarticSlot := Function.extend e Subtype.val (fun _ => .inl .bump)
  have hs (i : OSQuarticSlot) (hi : i ∈ U) : s (f i) = i := by
    change s (Function.extend Subtype.val e _ ((⟨i,hi⟩ : U) : OSQuarticSlot)) = i
    rw [Subtype.val_injective.extend_apply,show s (e ⟨i,hi⟩) = _ from he.extend_apply _ _ _]
  obtain ⟨ν,hν,hproj⟩ := osQuarticCountableGaussian hm hr s
  have hmap : Measurable (fun (x : ℕ → ℝ) => x ∘ f) := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  refine ⟨ν.map (fun x => x ∘ f), isProbabilityMeasure_map hmap.aemeasurable, ?_⟩
  intro I hI
  rw [Measure.map_map (Finset.measurable_restrict I) hmap]
  change ν.map (fun x => x ∘ (fun j : I => f j.val)) = _
  rw [osCountableProjection hm hr s ν hproj]
  have hslot : s ∘ (fun j : I => f j.val) = Subtype.val := funext fun j => hs j (hI j.2)
  rw [hslot]
  rfl

/-- A common probability law on all boundary and point slots, uniquely
determined on its cylinder sigma algebra by the explicit finite Gaussian
laws. Measurability of point evaluation jointly in space and sample
requires a modification and is not assumed in this construction. -/
theorem osQuarticGaussianProcess {m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    ∃! μ : Measure (OSQuarticSlot → ℝ), IsProjectiveLimit (α := fun _ => ℝ) μ (osGaussianFamily hm hr) := by
  classical
  let P := osGaussianFamily hm hr
  haveI (I : Finset OSQuarticSlot) : IsProbabilityMeasure (P I) :=
    @osQuarticFiniteLaw_probability I _ (Classical.decEq _) _ _ hm hr Subtype.val
  have hP : IsProjectiveMeasureFamily (α := fun _ => ℝ) P := osQuarticFiniteLaw_projective hm hr
  let C := projectiveFamilyContent hP
  have hzero {A : ℕ → Set (OSQuarticSlot → ℝ)} (hA : ∀ n, A n ∈ measurableCylinders (fun _ : OSQuarticSlot => ℝ))
      (ha : Antitone A) (he : ⋂ n, A n = ∅) : Tendsto (fun n => C (A n)) atTop (𝓝 0) := by
    choose s T hmT hAT using fun n => (mem_measurableCylinders _).mp (hA n)
    let U := ⋃ n, (s n : Set OSQuarticSlot)
    obtain ⟨ν,hν,hmap⟩ := osGaussianCountableCylinderLaw hm hr U (Set.countable_iUnion fun n => (s n).countable_toSet)
    have heq (n : ℕ) : C (A n) = ν (A n) := by
      rw [hAT,show C (cylinder (s n) (T n)) = _ from projectiveFamilyContent_cylinder hP (hmT n)]
      change osGaussianFamily hm hr (s n) (T n) = _
      rw [←hmap (s n) (Set.subset_iUnion (fun n => (s n : Set OSQuarticSlot)) n),
        Measure.map_apply (Finset.measurable_restrict _) (hmT n)]
      rfl
    simp_rw [heq]
    have hlim := tendsto_measure_iInter_atTop (μ := ν)
      (fun n => (MeasurableSet.of_mem_measurableCylinders (hA n)).nullMeasurableSet) ha ⟨0,measure_ne_top _ _⟩
    simpa only [he,measure_empty] using hlim
  have hSigma : C.IsSigmaSubadditive := by
    refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum isSetRing_measurableCylinders
      (fun f hf h_union hd => ?_)
    exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders C
      (fun _ _ => projectiveFamilyContent_ne_top _) (fun _ => hzero) hf h_union hd
  let μ := C.measure isSetSemiring_measurableCylinders generateFrom_measurableCylinders.ge hSigma
  have hμ : IsProjectiveLimit μ P := by
    intro I
    ext S hS
    rw [Measure.map_apply (Finset.measurable_restrict I) hS]
    change μ (cylinder I S) = P I S
    dsimp only [μ]
    rw [AddContent.measure_eq]
    · exact projectiveFamilyContent_cylinder hP hS
    · exact generateFrom_measurableCylinders.symm
    · exact cylinder_mem_measurableCylinders _ _ hS
  exact ⟨μ,hμ,fun ν hν => hν.unique hμ⟩

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
