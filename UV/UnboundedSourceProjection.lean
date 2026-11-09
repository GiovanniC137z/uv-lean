import UV.UnboundedSource

/-! Genuine orthogonal spectral-cut projections in the maximal L2 multiplier
model. The operators and all projection/commutation identities are derived
from measurable indicator multiplication. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

namespace UV

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem sourceL2Cut_add (s : Set X) (hs : MeasurableSet s) (f g : Lp ℂ 2 μ) :
    sourceL2Cut μ s hs (f+g) = sourceL2Cut μ s hs f + sourceL2Cut μ s hs g := by
  apply Lp.ext
  filter_upwards [sourceL2Cut_coe μ s hs (f+g),
    Lp.coeFn_add (sourceL2Cut μ s hs f) (sourceL2Cut μ s hs g),
    sourceL2Cut_coe μ s hs f, sourceL2Cut_coe μ s hs g,
    Lp.coeFn_add f g] with x hfg ha hf hg hadd
  simp only [Pi.add_apply] at ha hadd
  rw [hfg, ha, hf, hg]
  by_cases hx : x ∈ s
  · simpa only [indicator_of_mem hx] using hadd
  · simp only [indicator_of_notMem hx, add_zero]

theorem sourceL2Cut_smul (s : Set X) (hs : MeasurableSet s) (c : ℂ) (f : Lp ℂ 2 μ) :
    sourceL2Cut μ s hs (c • f) = c • sourceL2Cut μ s hs f := by
  apply Lp.ext
  filter_upwards [sourceL2Cut_coe μ s hs (c • f), Lp.coeFn_smul c (sourceL2Cut μ s hs f),
    sourceL2Cut_coe μ s hs f, Lp.coeFn_smul c f] with x hcf hs' hf hmul
  simp only [Pi.smul_apply] at hs' hmul
  rw [hcf, hs', hf]
  by_cases hx : x ∈ s <;> simp [hx, hmul]

theorem sourceL2Cut_norm_le (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    ‖sourceL2Cut μ s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [sourceL2Cut_coe μ s hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

def sourceL2CutLinear (s : Set X) (hs : MeasurableSet s) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := sourceL2Cut μ s hs
  map_add' := sourceL2Cut_add μ s hs
  map_smul' := sourceL2Cut_smul μ s hs

def sourceL2Projection (s : Set X) (hs : MeasurableSet s) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (sourceL2CutLinear μ s hs).mkContinuous 1 (fun f => by
    simpa only [one_mul] using sourceL2Cut_norm_le μ s hs f)

theorem sourceL2Projection_apply (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    sourceL2Projection μ s hs f = sourceL2Cut μ s hs f := rfl

theorem sourceL2Projection_norm_le (s : Set X) (hs : MeasurableSet s) :
    ‖sourceL2Projection μ s hs‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
    simpa only [one_mul] using sourceL2Cut_norm_le μ s hs f)

theorem sourceL2Cut_inter (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f : Lp ℂ 2 μ) :
    sourceL2Cut μ s hs (sourceL2Cut μ t ht f) = sourceL2Cut μ (s ∩ t) (hs.inter ht) f := by
  apply Lp.ext
  filter_upwards [sourceL2Cut_coe μ s hs (sourceL2Cut μ t ht f),
    sourceL2Cut_coe μ t ht f, sourceL2Cut_coe μ (s ∩ t) (hs.inter ht) f] with x hout hin hint
  rw [hout, hint]
  by_cases hx : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hx, hxt, hin]

theorem sourceL2Projection_mul (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    sourceL2Projection μ s hs * sourceL2Projection μ t ht =
      sourceL2Projection μ (s ∩ t) (hs.inter ht) := by
  apply ContinuousLinearMap.ext
  intro f
  exact sourceL2Cut_inter μ s t hs ht f

theorem sourceL2Projection_idempotent (s : Set X) (hs : MeasurableSet s) :
    sourceL2Projection μ s hs * sourceL2Projection μ s hs = sourceL2Projection μ s hs := by
  rw [sourceL2Projection_mul]
  simp only [inter_self]

theorem sourceL2Projection_commute (s t : Set X) (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    Commute (sourceL2Projection μ s hs) (sourceL2Projection μ t ht) := by
  change sourceL2Projection μ s hs * sourceL2Projection μ t ht =
    sourceL2Projection μ t ht * sourceL2Projection μ s hs
  rw [sourceL2Projection_mul, sourceL2Projection_mul]
  congr 1
  exact inter_comm s t

theorem sourceL2Projection_selfAdjoint (s : Set X) (hs : MeasurableSet s) :
    IsSelfAdjoint (sourceL2Projection μ s hs) := by
  change (sourceL2Projection μ s hs).adjoint = sourceL2Projection μ s hs
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  simp only [sourceL2Projection_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceL2Cut_coe μ s hs f, sourceL2Cut_coe μ s hs g] with x hf hg
  rw [hf, hg]
  by_cases hx : x ∈ s <;> simp [hx]

theorem sourceL2Projection_eq_self_iff (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    sourceL2Projection μ s hs f = f ↔ ∀ᵐ x ∂μ, x ∉ s → f x = 0 := by
  constructor
  · intro he
    filter_upwards [sourceL2Cut_coe μ s hs f] with x hx hxs
    change sourceL2Projection μ s hs f x = _ at hx
    rw [he] at hx
    simpa only [indicator_of_notMem hxs] using hx
  · intro hf
    apply Lp.ext
    filter_upwards [sourceL2Cut_coe μ s hs f, hf] with x hx hfx
    change sourceL2Cut μ s hs f x = f x
    rw [hx]
    by_cases hxs : x ∈ s
    · simp [hxs]
    · simp [hxs, hfx hxs]

/-- Every measurable cut preserves the actual maximal multiplier domain. -/
theorem sourceL2Projection_mem_domain (s : Set X) (hs : MeasurableSet s)
    (w : X → ℂ) (f : Lp ℂ 2 μ) (hf : f ∈ (sourceL2Multiplier μ w).domain) :
    sourceL2Projection μ s hs f ∈ (sourceL2Multiplier μ w).domain := by
  change MemLp (fun x => w x * sourceL2Cut μ s hs f x) 2 μ
  refine MemLp.ae_eq ?_ (hf.indicator hs)
  filter_upwards [sourceL2Cut_coe μ s hs f] with x hx
  change s.indicator (fun x => w x*f x) x = w x*sourceL2Cut μ s hs f x
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- Measurable-cut projection and maximal multiplication genuinely commute
on the maximal domain; this is the reducing property used by joint cuts. -/
theorem sourceL2Projection_reduce (s : Set X) (hs : MeasurableSet s)
    (w : X → ℂ) (f : Lp ℂ 2 μ) (hf : f ∈ (sourceL2Multiplier μ w).domain) :
    sourceL2Multiplier μ w
      ⟨sourceL2Projection μ s hs f, sourceL2Projection_mem_domain μ s hs w f hf⟩ =
      sourceL2Projection μ s hs (sourceL2Multiplier μ w ⟨f, hf⟩) := by
  apply Lp.ext
  filter_upwards [sourceL2Multiplier_coe μ w
      ⟨sourceL2Projection μ s hs f, sourceL2Projection_mem_domain μ s hs w f hf⟩,
    sourceL2Cut_coe μ s hs f, sourceL2Cut_coe μ s hs (sourceL2Multiplier μ w ⟨f,hf⟩),
    sourceL2Multiplier_coe μ w ⟨f,hf⟩] with x ht hcut hcutT hTf
  change (sourceL2Multiplier μ w
      ⟨sourceL2Projection μ s hs f, sourceL2Projection_mem_domain μ s hs w f hf⟩) x =
      sourceL2Cut μ s hs (sourceL2Multiplier μ w ⟨f,hf⟩) x
  rw [ht, hcutT]
  change w x*sourceL2Cut μ s hs f x = s.indicator (sourceL2Multiplier μ w ⟨f,hf⟩) x
  rw [hcut]
  by_cases hxs : x ∈ s
  · simpa only [indicator_of_mem hxs] using hTf.symm
  · simp [hxs]

def sourceSpectralProjection (w : X → ℝ) (hw : Measurable w)
    (B : Set ℝ) (hB : MeasurableSet B) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  sourceL2Projection μ (w ⁻¹' B) (hw hB)

theorem sourceL2Projection_empty :
    sourceL2Projection μ ∅ MeasurableSet.empty = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [sourceL2Cut_coe μ ∅ MeasurableSet.empty f,
    Lp.coeFn_zero ℂ 2 μ] with x hx hz
  change sourceL2Cut μ ∅ MeasurableSet.empty f x = (0 : Lp ℂ 2 μ) x
  rw [hx, hz]
  simp

theorem sourceL2Projection_univ :
    sourceL2Projection μ univ MeasurableSet.univ = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [sourceL2Cut_coe μ univ MeasurableSet.univ f] with x hx
  change sourceL2Cut μ univ MeasurableSet.univ f x = f x
  simpa only [indicator_univ] using hx

theorem sourceL2Projection_disjoint_union (s t : Set X) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hdis : Disjoint s t) :
    sourceL2Projection μ (s ∪ t) (hs.union ht) =
      sourceL2Projection μ s hs + sourceL2Projection μ t ht := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [sourceL2Cut_coe μ (s ∪ t) (hs.union ht) f,
    Lp.coeFn_add (sourceL2Cut μ s hs f) (sourceL2Cut μ t ht f),
    sourceL2Cut_coe μ s hs f, sourceL2Cut_coe μ t ht f] with x hu ha hs' ht'
  simp only [Pi.add_apply] at ha
  change sourceL2Cut μ (s ∪ t) (hs.union ht) f x =
    (sourceL2Cut μ s hs f+sourceL2Cut μ t ht f) x
  rw [hu, ha, hs', ht']
  exact congrFun (indicator_union_of_disjoint hdis (f : X → ℂ)) x

theorem sourceL2Projection_finite_union (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hdis : Pairwise (fun i j => Disjoint (s i) (s j))) (a : Finset ℕ) :
    sourceL2Projection μ (⋃ i ∈ a, s i)
      (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hs i) =
        ∑ i ∈ a, sourceL2Projection μ (s i) (hs i) := by
  classical
  induction a using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, Finset.sum_empty]
    exact sourceL2Projection_empty μ
  | @insert i a hi ih =>
    have hia : Disjoint (s i) (⋃ j ∈ a, s j) := by
      apply Set.disjoint_iUnion_right.mpr
      intro j
      apply Set.disjoint_iUnion_right.mpr
      intro hj
      apply hdis
      intro hij
      exact hi (hij ▸ hj)
    simp only [Finset.set_biUnion_insert, Finset.sum_insert hi]
    rw [sourceL2Projection_disjoint_union μ _ _ (hs i)
      (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hs j) hia, ih]

/-- Increasing countable unions converge strongly on every L2 vector.
The proof uses actual L2-norm convergence, not pointwise convergence alone. -/
theorem sourceL2Projection_tendsto_iUnion (s : ℕ → Set X)
    (hs : ∀ n, MeasurableSet (s n)) (hmono : Monotone s) (f : Lp ℂ 2 μ) :
    Tendsto (fun n => sourceL2Projection μ (s n) (hs n) f) atTop
      (𝓝 (sourceL2Projection μ (⋃ n, s n) (MeasurableSet.iUnion hs) f)) := by
  let U := ⋃ n, s n
  have hU : MeasurableSet U := MeasurableSet.iUnion hs
  let q : ℕ → Set X := fun n => s n ∪ Uᶜ
  have hq (n : ℕ) : MeasurableSet (q n) := (hs n).union hU.compl
  have hcover : ∀ᵐ x ∂μ, ∃ N : ℕ, ∀ n ≥ N, x ∈ q n := by
    filter_upwards with x
    by_cases hx : x ∈ U
    · obtain ⟨N, hN⟩ := mem_iUnion.mp hx
      exact ⟨N, fun n hn => Or.inl (hmono hn hN)⟩
    · exact ⟨0, fun _ _ => Or.inr hx⟩
  have he (n : ℕ) : sourceL2Cut μ (q n) (hq n) (sourceL2Cut μ U hU f) =
      sourceL2Cut μ (s n) (hs n) f := by
    rw [sourceL2Cut_inter]
    have hset : q n ∩ U = s n := by
      ext x
      constructor
      · rintro ⟨hx, hxU⟩
        exact hx.elim id (fun hc => (hc hxU).elim)
      · intro hx
        exact ⟨Or.inl hx, mem_iUnion.mpr ⟨n, hx⟩⟩
    congr 1
  have hlim := sourceL2Cut_tendsto μ q hq hcover (sourceL2Cut μ U hU f)
  simpa only [he, sourceL2Projection_apply] using hlim

/-- Countable disjoint spectral cuts add strongly: actual finite projection
sums converge in L2 norm to the projection on their union. -/
theorem sourceL2Projection_countable_disjoint (s : ℕ → Set X)
    (hs : ∀ n, MeasurableSet (s n))
    (hdis : Pairwise (fun i j => Disjoint (s i) (s j))) (f : Lp ℂ 2 μ) :
    Tendsto (fun N => ∑ i ∈ Finset.range N, sourceL2Projection μ (s i) (hs i) f)
      atTop (𝓝 (sourceL2Projection μ (⋃ i, s i) (MeasurableSet.iUnion hs) f)) := by
  let u : ℕ → Set X := fun N => ⋃ i ∈ Finset.range N, s i
  have hu (N : ℕ) : MeasurableSet (u N) :=
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hs i
  have hmono : Monotone u := by
    intro M N hMN x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨hiM, hix⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_range.mpr
      ((Finset.mem_range.mp hiM).trans_le hMN), hix⟩⟩
  have hU : (⋃ N, u N) = ⋃ i, s i := by
    ext x
    constructor
    · intro hx
      obtain ⟨N, hN⟩ := mem_iUnion.mp hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hN
      obtain ⟨_, hix⟩ := mem_iUnion.mp hi
      exact mem_iUnion.mpr ⟨i, hix⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i+1, mem_iUnion.mpr ⟨i,
        mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self i), hi⟩⟩⟩
  have he (N : ℕ) : sourceL2Projection μ (u N) (hu N) f =
      ∑ i ∈ Finset.range N, sourceL2Projection μ (s i) (hs i) f := by
    have hp := sourceL2Projection_finite_union μ s hs hdis (Finset.range N)
    have h := congrArg (fun P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ => P f) hp
    simpa only [ContinuousLinearMap.sum_apply] using h
  have hEnd : sourceL2Projection μ (⋃ N, u N) (MeasurableSet.iUnion hu) =
      sourceL2Projection μ (⋃ i, s i) (MeasurableSet.iUnion hs) := by congr 1
  have hlim := sourceL2Projection_tendsto_iUnion μ u hu hmono f
  simpa only [he, hEnd] using hlim

/-- The genuine spectral cut projections of any two measurable multipliers
commute. No projection identity is assumed in the construction. -/
theorem sourceSpectralProjection_strong_commute (u v : X → ℝ)
    (hu : Measurable u) (hv : Measurable v) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Commute (sourceSpectralProjection μ u hu A hA) (sourceSpectralProjection μ v hv B hB) :=
  sourceL2Projection_commute μ (u ⁻¹' A) (v ⁻¹' B) (hu hA) (hv hB)

end UV
