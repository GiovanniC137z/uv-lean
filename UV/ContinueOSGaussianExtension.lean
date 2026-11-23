import UV.ContinueOSGaussianCountable

/-! Gaussian extension for any real positive covariance kernel, including
the square-integrable Fourier form domain of the massive boundary field. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Finset Set Matrix
open scoped ENNReal Topology Matrix

namespace UV

structure OSPositiveCovariance (α : Type) where
  entry : α → α → ℝ
  pos : ∀ {ι : Type} [Fintype ι] (s : ι → α), Matrix.PosSemidef (R := ℝ) fun i j => entry (s i) (s j)

variable {α : Type}

def OSPositiveCovariance.law (Q : OSPositiveCovariance α) {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι → α) := MarkedPhoton.photonProjectionLaw _ (Q.pos s)

instance OSPositiveCovariance.law_probability (Q : OSPositiveCovariance α) {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι → α) : IsProbabilityMeasure (Q.law s) := MarkedPhoton.physicalLaw_probability _ _

theorem OSPositiveCovariance.law_map (Q : OSPositiveCovariance α) {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (s : ι → α) (f : κ → ι) :
    (Q.law s).map (fun x => x ∘ f) = Q.law (s ∘ f) := osFiniteGaussian_map _ _ _ _

abbrev OSPositiveCovariance.family (Q : OSPositiveCovariance α) (J : Finset α) :=
  @OSPositiveCovariance.law α Q J _ (Classical.decEq _) Subtype.val

theorem OSPositiveCovariance.projective (Q : OSPositiveCovariance α) :
    IsProjectiveMeasureFamily (α := fun _ => ℝ) Q.family := by
  classical
  intro I J h
  exact (Q.law_map (fun i : I => i.val) (fun j : J => ⟨j.val,h j.2⟩)).symm

private theorem OSPositiveCovariance.countableGaussian (Q : OSPositiveCovariance α) (s : ℕ → α) :
    ∃ μ : Measure (ℕ → ℝ), IsProbabilityMeasure μ ∧ IsProjectiveLimit (α := fun _ => ℝ) μ
      (fun J => Q.law (fun j : J => s j)) := by
  let P (J : Finset ℕ) := Q.law (fun j : J => s j)
  haveI (J : Finset ℕ) : IsProbabilityMeasure (P J) := Q.law_probability _
  have hP : IsProjectiveMeasureFamily (α := fun _ => ℝ) P := by
    intro I J hJI
    exact (Q.law_map (fun a : I => s a) (fun j : J => ⟨j.1,hJI j.2⟩)).symm
  obtain ⟨μ,hμ⟩ := osCountableExtension P hP
  exact ⟨μ,hμ.isProbabilityMeasure,hμ⟩

private theorem osPositiveCountableProjection (Q : OSPositiveCovariance α) (s : ℕ → α)
    (μ : Measure (ℕ → ℝ)) (hμ : IsProjectiveLimit (α := fun _ => ℝ) μ (fun J =>
      Q.law (fun j : J => s j))) {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℕ) :
    μ.map (fun x => x ∘ f) = Q.law (s ∘ f) := by
  let U := Finset.univ.image f
  let l (i : ι) : U := ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have me : Measurable (fun (x : U → ℝ) => x ∘ l) := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  calc
    _ = (μ.map U.restrict).map (fun x => x ∘ l) := (Measure.map_map me (Finset.measurable_restrict U)).symm
    _ = _ := by rw [hμ]; exact Q.law_map (fun j : U => s j) l

variable [Inhabited α]

private theorem osPositiveCountableCylinderLaw (Q : OSPositiveCovariance α)
    (U : Set α) (hU : U.Countable) :
    ∃ μ : Measure (α → ℝ), IsProbabilityMeasure μ ∧
      ∀ (I : Finset α), (I : Set α) ⊆ U →
        μ.map I.restrict = Q.family I := by
  classical
  letI : Countable U := hU
  obtain ⟨e,he⟩ := Countable.exists_injective_nat U
  let f : α → ℕ := Function.extend Subtype.val e (fun _ => 0)
  let s : ℕ → α := Function.extend e Subtype.val (fun _ => default)
  have hs (i : α) (hi : i ∈ U) : s (f i) = i := by
    change s (Function.extend Subtype.val e _ ((⟨i,hi⟩ : U) : α)) = i
    rw [Subtype.val_injective.extend_apply,show s (e ⟨i,hi⟩) = _ from he.extend_apply _ _ _]
  obtain ⟨ν,hν,hproj⟩ := Q.countableGaussian s
  have hmap : Measurable (fun (x : ℕ → ℝ) => x ∘ f) := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  refine ⟨ν.map (fun x => x ∘ f), isProbabilityMeasure_map hmap.aemeasurable, ?_⟩
  intro I hI
  rw [Measure.map_map (Finset.measurable_restrict I) hmap]
  change ν.map (fun x => x ∘ (fun j : I => f j.val)) = _
  rw [osPositiveCountableProjection Q s ν hproj]
  have hslot : s ∘ (fun j : I => f j.val) = Subtype.val := funext fun j => hs j (hI j.2)
  rw [hslot]
  rfl

/-- A common probability law on all boundary and point slots, uniquely
determined on its cylinder sigma algebra by the explicit finite Gaussian
laws. Measurability of point evaluation jointly in space and sample
requires a modification and is not assumed in this construction. -/
theorem osPositiveGaussianProcess (Q : OSPositiveCovariance α) :
    ∃! μ : Measure (α → ℝ), IsProjectiveLimit (α := fun _ => ℝ) μ (Q.family) := by
  classical
  let P := Q.family
  haveI (I : Finset α) : IsProbabilityMeasure (P I) :=
    @OSPositiveCovariance.law_probability α Q I _ (Classical.decEq _) Subtype.val
  have hP : IsProjectiveMeasureFamily (α := fun _ => ℝ) P := Q.projective
  let C := projectiveFamilyContent hP
  have hzero {A : ℕ → Set (α → ℝ)} (hA : ∀ n, A n ∈ measurableCylinders (fun _ : α => ℝ))
      (ha : Antitone A) (he : ⋂ n, A n = ∅) : Tendsto (fun n => C (A n)) atTop (𝓝 0) := by
    choose s T hmT hAT using fun n => (mem_measurableCylinders _).mp (hA n)
    let U := ⋃ n, (s n : Set α)
    obtain ⟨ν,hν,hmap⟩ := osPositiveCountableCylinderLaw Q U (Set.countable_iUnion fun n => (s n).countable_toSet)
    have heq (n : ℕ) : C (A n) = ν (A n) := by
      rw [hAT,show C (cylinder (s n) (T n)) = _ from projectiveFamilyContent_cylinder hP (hmT n)]
      change Q.family (s n) (T n) = _
      rw [←hmap (s n) (Set.subset_iUnion (fun n => (s n : Set α)) n),
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

omit [Inhabited α] in
/-- A finite observable list can repeat coordinates in any order on the
common sample space. -/
theorem osPositiveGaussian_projection (Q : OSPositiveCovariance α)
    (μ : Measure (α → ℝ)) (hμ : IsProjectiveLimit (α := fun _ => ℝ) μ (Q.family))
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι → α) :
    μ.map (fun x => x ∘ s) = Q.law s := by
  classical
  let U := Finset.univ.image s
  let l (i : ι) : U := ⟨s i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have me : Measurable (fun (x : U → ℝ) => x ∘ l) := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  calc
    _ = (μ.map U.restrict).map (fun x => x ∘ l) := (Measure.map_map me (Finset.measurable_restrict U)).symm
    _ = _ := by
      rw [hμ]
      exact @OSPositiveCovariance.law_map α Q U ι _ _ (Classical.decEq _) _ Subtype.val l

end UV
