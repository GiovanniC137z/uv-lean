import UV.ContinueOpeningCoordinateCalc

/-! The normalized projection measure and bounded Borel calculus of an
actual real multiplication coordinate, including measurable rescalings. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ComplexConjugate
namespace UV

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

private theorem opening_projection_hasSum (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (ψ : Lp ℂ 2 μ) :
    HasSum (fun n => sourceL2Projection μ (s n) (hs n) ψ)
      (sourceL2Projection μ (⋃ n, s n) (MeasurableSet.iUnion hs) ψ) := by
  classical
  let U := ⋃ n, s n
  let S := fun a : Finset ℕ => ⋃ i ∈ a, s i
  have hS a : MeasurableSet (S a) := MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hs i
  have hSU a : S a ⊆ U := fun x hx => by
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    obtain ⟨_,hx⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨i,hx⟩
  have he a : (∑ i ∈ a, sourceL2Projection μ (s i) (hs i) ψ : Lp ℂ 2 μ) = sourceL2Projection μ (S a) (hS a) ψ := by
    rw [←ContinuousLinearMap.sum_apply,←sourceL2Projection_finite_union μ s hs hd]
  have hA a : ((∑ i ∈ a, sourceL2Projection μ (s i) (hs i) ψ : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] (S a).indicator ψ := by
    rw [he]
    exact sourceL2Cut_coe μ (S a) (hS a) ψ
  have hB := sourceL2Cut_coe μ U (MeasurableSet.iUnion hs) ψ
  apply opening_l2_dominated μ atTop _ _ _ _ hA hB (fun u => ‖ψ u‖^2)
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ψ)).mp (Lp.memLp ψ))
  · intro a
    apply ae_of_all
    intro u
    by_cases h : u ∈ S a
    · simp [h,hSU a h]
    · by_cases k : u ∈ U <;> simp [h,k]
  · apply ae_of_all
    intro u
    apply tendsto_const_nhds.congr'
    by_cases h : u ∈ U
    · obtain ⟨i,hi⟩ := mem_iUnion.mp h
      filter_upwards [eventually_ge_atTop ({i} : Finset ℕ)] with a ha
      have hu : u ∈ S a := mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨ha (Finset.mem_singleton_self _),hi⟩⟩
      simp [hu,h]
    · exact Eventually.of_forall fun a => by simp [h,show u ∉ S a from fun hu => h (hSU a hu)]

def openingCoordinatePVM (w : X → ℝ) (hw : Measurable w) : SourcePVM (Lp ℂ 2 μ) := by
  classical
  exact
    { projection := fun s => if h : MeasurableSet s then sourceL2Projection μ (w ⁻¹' s) (hw h) else 0
      empty := by simpa using sourceL2Projection_empty μ
      univ := by simpa using sourceL2Projection_univ μ
      selfAdjoint := fun s hs => by simpa only [dif_pos hs] using sourceL2Projection_selfAdjoint μ _ (hw hs)
      inter := fun s t hs ht => by
        simp only [dif_pos (hs.inter ht),dif_pos hs,dif_pos ht]
        exact (sourceL2Projection_mul μ _ _ (hw hs) (hw ht)).symm
      countable := fun s hs hd x => by
        simp only [dif_pos (hs _),dif_pos (MeasurableSet.iUnion hs),preimage_iUnion]
        exact opening_projection_hasSum μ (fun i => w ⁻¹' s i) (fun i => hw (hs i)) (fun i j hij => (hd hij).preimage w) x }

theorem opening_coordinate_projection_ae (w : X → ℝ) (hw : Measurable w) {s : Set ℝ} (hs : MeasurableSet s)
    (x : Lp ℂ 2 μ) :
    ((openingCoordinatePVM μ w hw).projection s x : X → ℂ) =ᵐ[μ] (w ⁻¹' s).indicator x := by
  classical
  unfold openingCoordinatePVM
  simp only [dif_pos hs]
  exact sourceL2Cut_coe μ (w ⁻¹' s) (hw hs) x

def openingCoordinateBorel (w : X → ℝ) (hw : Measurable w) : SourceBorelCalculus (openingCoordinatePVM μ w hw) where
  operator := openingCoordinateAction μ w hw
  indicator := fun s hs => by
    ext x : 1
    apply Lp.ext
    filter_upwards [opening_coordinate_action_ae μ w hw (sourceBoundedBorel_indicator hs) x,
      opening_coordinate_projection_ae μ w hw hs x] with u ha hb
    rw [ha,hb]
    by_cases h : w u ∈ s <;> simp [h]
  add := fun f g hf hg => by
    ext x : 1
    apply Lp.ext
    filter_upwards [opening_coordinate_action_ae μ w hw (sourceBoundedBorel_add hf hg) x,
      opening_coordinate_action_ae μ w hw hf x,opening_coordinate_action_ae μ w hw hg x,
      Lp.coeFn_add (openingCoordinateAction μ w hw f x) (openingCoordinateAction μ w hw g x)] with u hfg hf' hg' ha
    change _ = ((openingCoordinateAction μ w hw f x)+(openingCoordinateAction μ w hw g x)) u
    rw [hfg,ha]
    simp [hf',hg',add_mul]
  smul := fun a f hf => by
    ext x : 1
    apply Lp.ext
    filter_upwards [opening_coordinate_action_ae μ w hw (sourceBoundedBorel_smul a hf) x,
      opening_coordinate_action_ae μ w hw hf x,Lp.coeFn_smul (a:ℂ) (openingCoordinateAction μ w hw f x)] with u h ha hs
    change _ = ((a:ℂ) • (openingCoordinateAction μ w hw f x)) u
    rw [h,hs]
    simp [ha,mul_assoc]
  mul := fun f g hf hg => by
    ext x : 1
    apply Lp.ext
    filter_upwards [opening_coordinate_action_ae μ w hw (sourceBoundedBorel_mul hf hg) x,
      opening_coordinate_action_ae μ w hw hf (openingCoordinateAction μ w hw g x),
      opening_coordinate_action_ae μ w hw hg x] with u h hgf hg'
    change _ = (openingCoordinateAction μ w hw f (openingCoordinateAction μ w hw g x)) u
    rw [h,hgf,hg']
    simp [mul_assoc]
  selfAdjoint := fun f hf => by
    change (openingCoordinateAction μ w hw f).adjoint = _
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [opening_coordinate_action_ae μ w hw hf x,opening_coordinate_action_ae μ w hw hf y] with u hx hy
    rw [hx,hy]
    simp [RCLike.inner_apply,mul_left_comm,mul_assoc]
  norm_le := fun f C hM hC hB => by
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro x
    have he : C*‖x‖ = ‖(C:ℂ) • x‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]
    rw [he]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [opening_coordinate_action_ae μ w hw ⟨hM,C,hC,hB⟩ x,Lp.coeFn_smul (C:ℂ) x] with u h k
    rw [h,k]
    simp only [Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  strong_limit := opening_coordinate_action_strong μ w hw atTop

end UV
