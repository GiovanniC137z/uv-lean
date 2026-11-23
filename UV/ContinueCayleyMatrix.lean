import UV.ContinueCayleyState
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.Analysis.Matrix.Order

/-! Polarization of the compact scalar spectral states. Complex measures are
identified by their continuous tests through closed-set approximation and
countable additivity on the generated Borel sigma-algebra. -/

noncomputable section
open MeasureTheory Set Filter ContinuousLinearMap Matrix
open scoped Topology InnerProductSpace ComplexConjugate ComplexOrder ENNReal Matrix
namespace UV.SectorPlane

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] [HasOuterApproxClosed X]

def closingClosedTest {S : Set X} (h : IsClosed S) (n : ℕ) : C(X,ℂ) :=
  ⟨fun x => ((h.apprSeq n x : ℝ) : ℂ), by fun_prop⟩

/-- A finite complex measure together with its continuous-test integrals.
The closed-set limit makes the pairing uniquely determine the measure. -/
def closingMeasurePairing (X : Type*) [TopologicalSpace X] [MeasurableSpace X] [HasOuterApproxClosed X] :
    Submodule ℂ (ComplexMeasure X × (C(X,ℂ) → ℂ)) where
  carrier := {p | ∀ (s : Set X) (hs : IsClosed s), Tendsto (fun n => p.2 (closingClosedTest hs n)) atTop (𝓝 (p.1 s))}
  zero_mem' := fun _ _ => tendsto_const_nhds
  add_mem' := fun {_ _} ha hb s hs => (ha s hs).add (hb s hs)
  smul_mem' := fun c _ ha s hs => (ha s hs).const_mul c

def closingPositivePairing (μ : Measure X) [IsFiniteMeasure μ] : closingMeasurePairing X := by
  refine ⟨(μ.toSignedMeasure.toComplexMeasure 0, fun f => ∫ x, f x ∂μ),?_⟩
  intro s hs
  change Tendsto (fun n => ∫ x, closingClosedTest hs n x ∂μ) atTop (𝓝 _)
  have ht := HasOuterApproxClosed.tendsto_lintegral_apprSeq hs μ
  have hR := (ENNReal.tendsto_toReal (measure_ne_top μ s)).comp ht
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hR
  have hn (n : ℕ) : (∫ x, closingClosedTest hs n x ∂μ) = (((∫⁻ x, (hs.apprSeq n x:ℝ≥0∞) ∂μ).toReal:ℝ):ℂ) := by
    change (∫ x, ((hs.apprSeq n x:ℝ):ℂ) ∂μ)=_
    rw [integral_complex_ofReal,integral_eq_lintegral_of_nonneg_ae]
    · simp
    · exact ae_of_all _ (fun x => (hs.apprSeq n x).property)
    · exact (NNReal.continuous_coe.comp (hs.apprSeq n).continuous).aestronglyMeasurable
  simp_rw [hn]
  simpa only [Function.comp_def,SignedMeasure.toComplexMeasure_apply,Measure.toSignedMeasure_apply_measurable hs.measurableSet,
    VectorMeasure.zero_apply,Measure.real] using hc

omit [CompactSpace X] [T2Space X] in
theorem closing_pairing_unique (a b : closingMeasurePairing X) (he : a.val.2=b.val.2) :
    a.val.1=b.val.1 := by
  have hc (s : Set X) (h : IsClosed s) : a.val.1 s=b.val.1 s := by
    apply tendsto_nhds_unique (a.property s h)
    simpa only [he] using b.property s h
  apply VectorMeasure.ext
  refine MeasurableSpace.induction_on_inter (C := fun s _ => a.val.1 s=b.val.1 s)
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed ?_ ?_ ?_ ?_
  · simp
  · exact hc
  · intro s hs hh
    have h := hc univ isClosed_univ
    rw [←compl_union_self s,a.val.1.of_union disjoint_compl_left hs.compl hs,b.val.1.of_union disjoint_compl_left hs.compl hs,hh] at h
    exact add_right_cancel h
  · intro s hd hs ih
    rw [a.val.1.of_disjoint_iUnion hs hd,b.val.1.of_disjoint_iUnion hs hd]
    exact tsum_congr ih

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def closingPolarPairing (P : H → closingMeasurePairing X) (u v : H) : closingMeasurePairing X :=
  (1/4:ℂ) • (P (u+v)-P (u-v)-Complex.I • (P (u+Complex.I • v)-P (u-Complex.I • v)))

def closingCompactPolar (π : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (u v : H) : closingMeasurePairing X :=
  closingPolarPairing (fun a => closingPositivePairing (closingCompactState π a)) u v

theorem closing_polar_integral (π : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (u v : H) (f : C(X,ℂ)) :
    (closingCompactPolar π u v).val.2 f = ⟪u, π f v⟫_ℂ := by
  change (1/4:ℂ)*(((∫ x, f x ∂closingCompactState π (u+v))-(∫ x, f x ∂closingCompactState π (u-v)))-
    Complex.I*((∫ x, f x ∂closingCompactState π (u+Complex.I • v))-(∫ x, f x ∂closingCompactState π (u-Complex.I • v))))=_
  simp only [closing_compact_state_integral,map_add,map_sub,map_smul,inner_add_left,inner_add_right,
    inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq]
  ring

omit [CompactSpace X] [T2Space X] [CompleteSpace H] [BorelSpace X] in
theorem closing_polar_test_general (P : H → closingMeasurePairing X)
    (L : C(X,ℂ) → (H →L[ℂ] H))
    (h : ∀ x f, (P x).val.2 f = ⟪x,L f x⟫_ℂ) (u v : H) (f : C(X,ℂ)) :
    (closingPolarPairing P u v).val.2 f = ⟪u,L f v⟫_ℂ := by
  change (1/4:ℂ)*(((P (u+v)).val.2 f - (P (u-v)).val.2 f)-
    Complex.I*((P (u+Complex.I • v)).val.2 f-(P (u-Complex.I • v)).val.2 f))=_
  simp only [h,map_add,map_sub,map_smul,inner_add_left,inner_add_right,
    inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq]
  ring

variable {ι : Type*} [Fintype ι]

private def testMap (f : C(X,ℂ)) : closingMeasurePairing X →ₗ[ℂ] ℂ :=
  ⟨⟨fun a => a.val.2 f,fun _ _ => rfl⟩,fun _ _ => rfl⟩

private def massMap : closingMeasurePairing X →ₗ[ℂ] ComplexMeasure X :=
  ⟨⟨fun a => a.val.1,fun _ _ => rfl⟩,fun _ _ => rfl⟩

omit [CompactSpace X] [T2Space X] [CompleteSpace H] in
theorem closing_polar_quadratic_measure (P : H → closingMeasurePairing X)
    (L : C(X,ℂ) → (H →L[ℂ] H)) (h : ∀ x f, (P x).val.2 f = ⟪x,L f x⟫_ℂ)
    (p : ι → H) (v : ι → ℂ) :
    (∑ i, ∑ j, (conj (v i)*v j) • (closingPolarPairing P (p i) (p j)).val.1) =
      (P (∑ i,v i • p i)).val.1 := by
  let C := ∑ i, ∑ j, (conj (v i)*v j) • closingPolarPairing P (p i) (p j)
  have he : C.val.2=(P (∑ i,v i • p i)).val.2 := by
    funext f
    change testMap f C = _
    rw [h, sum_inner]
    simp only [C,map_sum,map_smul,smul_eq_mul,inner_smul_left,inner_sum,inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show testMap f (closingPolarPairing P (p i) (p j))=_ from closing_polar_test_general P L h _ _ _]
    ring
  have hm : massMap C = (P (∑ i,v i • p i)).val.1 := closing_pairing_unique C _ he
  simpa only [C,map_sum,map_smul] using hm

theorem closing_compact_quadratic_measure (π : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (p : ι → H) (v : ι → ℂ) :
    (∑ i, ∑ j, (conj (v i)*v j) • (closingCompactPolar π (p i) (p j)).val.1) =
      (closingPositivePairing (closingCompactState π (∑ i, v i • p i))).val.1 :=
  closing_polar_quadratic_measure _ (fun f => π f) (fun x f => closing_compact_state_integral π x f) p v

def closingSetEval {Y : Type*} [MeasurableSpace Y] (s : Set Y) : ComplexMeasure Y →ₗ[ℂ] ℂ :=
  ⟨⟨fun a => a s,fun _ _ => rfl⟩,fun _ _ => rfl⟩

omit [CompactSpace X] [T2Space X] [CompleteSpace H] in
theorem closing_polar_quadratic_set (P : H → closingMeasurePairing X)
    (L : C(X,ℂ) → (H →L[ℂ] H)) (h : ∀ x f, (P x).val.2 f = ⟪x,L f x⟫_ℂ)
    (p : ι → H) (v : ι → ℂ) (s : Set X) :
    (∑ i, ∑ j, (conj (v i)*v j) * (closingPolarPairing P (p i) (p j)).val.1 s) =
      (P (∑ i,v i • p i)).val.1 s := by
  have hh := congrArg (closingSetEval s) (closing_polar_quadratic_measure P L h p v)
  simpa only [map_sum,map_smul,smul_eq_mul] using hh

open scoped ComplexOrder in
theorem closing_matrix_positive_of_quadratic (M : Matrix ι ι ℂ)
    (h : ∀ v : ι → ℂ, ∃ r : ℝ, 0≤r ∧ (∑ i,∑ j,(conj (v i)*v j)*M i j)=(r:ℂ)) :
    M.PosSemidef := by
  classical
  have hx (v : ι → ℂ) : ∃ r : ℝ, 0≤r ∧ star v ⬝ᵥ (M *ᵥ v)=(r:ℂ) := by
    obtain ⟨r,hr,he⟩ := h v
    refine ⟨r,hr,?_⟩
    rw [←he]
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,Complex.star_def,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  constructor
  · apply Matrix.isHermitian_iff_isSymmetric.mpr
    apply (LinearMap.isSymmetric_iff_inner_map_self_real _).mpr
    intro x
    obtain ⟨v,rfl⟩ := (WithLp.toLp_surjective (V:=ι→ℂ) 2) x
    obtain ⟨r,_,hr⟩ := hx v
    have hvr : ⟪WithLp.toLp 2 v,M.toEuclideanLin (WithLp.toLp 2 v)⟫_ℂ=(r:ℂ) := by
      simpa only [Matrix.toEuclideanLin_toLp,Matrix.toLin'_apply,EuclideanSpace.inner_eq_star_dotProduct,
        WithLp.ofLp_toLp,dotProduct_comm (M *ᵥ v)] using hr
    rw [inner_conj_symm, hvr]
    have hvrc := congrArg (starRingEnd ℂ) hvr
    rw [inner_conj_symm,Complex.conj_ofReal] at hvrc
    exact hvrc.symm
  · intro v
    obtain ⟨r,hr,hv⟩ := hx v
    rw [hv]; exact_mod_cast hr

theorem closing_compact_matrix_positive (π : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (p : ι → H) {s : Set X} (hs : MeasurableSet s) :
    Matrix.PosSemidef (fun i j => (closingCompactPolar π (p i) (p j)).val.1 s) := by
  apply closing_matrix_positive_of_quadratic
  intro v
  have he := closing_polar_quadratic_set (fun x => closingPositivePairing (closingCompactState π x))
    (fun f => π f) (fun x f => closing_compact_state_integral π x f) p v s
  refine ⟨(closingCompactState π (∑ i,v i • p i)).real s,measureReal_nonneg,he.trans ?_⟩
  change (closingCompactState π _).toSignedMeasure.toComplexMeasure 0 s = _
  simp [SignedMeasure.toComplexMeasure_apply,hs]
  rfl

end UV.SectorPlane
