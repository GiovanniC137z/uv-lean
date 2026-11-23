import UV.ContinueNormalCircleCoordinates

/-! The marked internal positions of the open Dirac chain are integrated
with both physical endpoints fixed, including when they coincide. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

attribute [local instance] Real.fact_zero_lt_one

local instance normalOpenCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

def normalAnchoredVertices {n : ℕ} (e : UnitAddCircle) (x : Fin n → UnitAddCircle) : Fin (n+1) → UnitAddCircle :=
  Fin.snoc (α := fun _ => UnitAddCircle) x e

def normalEndpointDifferences {n : ℕ} (e : UnitAddCircle) (x : Fin n → UnitAddCircle) : Fin n → UnitAddCircle :=
  normalCircleDifferences (normalAnchoredVertices e x)

theorem normal_anchored_vertices_add {n : ℕ} (a b : UnitAddCircle) (x y : Fin n → UnitAddCircle) :
    normalAnchoredVertices (a+b) (x+y) = normalAnchoredVertices a x + normalAnchoredVertices b y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [normalAnchoredVertices]

theorem normal_endpoint_differences_preserving {n : ℕ} (e : UnitAddCircle) :
    MeasurePreserving (normalEndpointDifferences (n := n) e) := by
  let F : (Fin n → UnitAddCircle) →+ (Fin n → UnitAddCircle) :=
    { toFun := normalEndpointDifferences 0
      map_zero' := by
        have h : normalAnchoredVertices 0 (0 : Fin n → UnitAddCircle) = 0 := by
          funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [normalAnchoredVertices]
        funext j
        simp [normalEndpointDifferences,h,normalCircleDifferences]
      map_add' := fun x y => by
        have h := normal_anchored_vertices_add (0 : UnitAddCircle) 0 x y
        rw [zero_add] at h
        funext j
        simp only [normalEndpointDifferences,normalCircleDifferences,h,Pi.add_apply]
        abel }
  have hc (i : Fin (n+1)) : Continuous (fun x : Fin n → UnitAddCircle => normalAnchoredVertices 0 x i) := by
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [normalAnchoredVertices] <;> fun_prop
  have hF : Continuous F := continuous_pi fun j => (hc j.succ).sub (hc j.castSucc)
  have hs : Function.Surjective F := by
    intro t
    let v := fun i : Fin (n+1) => Fin.partialSum t i - Fin.partialSum t (Fin.last n)
    have he : v (Fin.last n) = 0 := by simp [v]
    have hh : normalAnchoredVertices 0 (Fin.init v) = v := by
      rw [←he]; exact Fin.snoc_init_self v
    refine ⟨Fin.init v,funext fun j => ?_⟩
    change normalAnchoredVertices 0 (Fin.init v) j.succ-normalAnchoredVertices 0 (Fin.init v) j.castSucc = t j
    simp only [hh,v,Fin.partialSum_succ]; abel
  let μ := (volume : Measure (Fin n → UnitAddCircle))
  haveI : IsAddLeftInvariant (μ.map F) := isAddLeftInvariant_map F.toAddHom hF.measurable hs
  haveI : IsProbabilityMeasure (μ.map F) := Measure.isProbabilityMeasure_map hF.measurable.aemeasurable
  have h := isAddLeftInvariant_eq_smul (μ.map F) μ
  have hc' := congrArg (fun ν : Measure (Fin n → UnitAddCircle) => ν univ) h
  simp only [measure_univ,Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,mul_one] at hc'
  have hscalar : (μ.map F).addHaarScalarFactor μ = 1 := by exact_mod_cast hc'.symm
  have hmp : MeasurePreserving F := ⟨hF.measurable,by simpa only [hscalar,one_smul] using h⟩
  let y : Fin n → UnitAddCircle := fun _ => -e
  have heq : normalEndpointDifferences (n := n) e = F ∘ (fun x => x+y) := by
    funext x j
    have hz : normalAnchoredVertices 0 (x+y) = fun i => normalAnchoredVertices e x i-e := by
      funext i
      refine Fin.lastCases ?_ (fun k => ?_) i <;> simp [normalAnchoredVertices,y,sub_eq_add_neg]
    change normalAnchoredVertices e x j.succ-normalAnchoredVertices e x j.castSucc =
      normalAnchoredVertices 0 (x+y) j.succ-normalAnchoredVertices 0 (x+y) j.castSucc
    rw [hz]
    exact (sub_sub_sub_cancel_right _ _ _).symm
  rw [heq]
  exact hmp.comp (measurePreserving_add_right volume y)

local instance normalOpenPositionMatrixMeasurable : MeasurableSpace DiracMatrix := borel _
local instance normalOpenPositionMatrixBorel : BorelSpace DiracMatrix := ⟨rfl⟩

def normalQuotientOpenWord {n : ℕ} (m L θ : ℝ) (δ : UnitAddCircle) (u : Fin n → UnitVector OSFourSpace)
    (p : Fin (n+1) → OSFourSpace) (t : Fin n → UnitAddCircle) : DiracMatrix :=
  normalOrderedWord (fun i => normalQuotientKernel m L θ (p i)
    (Fin.cons (α := fun _ => UnitAddCircle) (δ-∑ j, t j) t i) * normalOpenVertex u i)

/-- The charged line goes from a through the n marked internal positions
to e. The last propagator carries the endpoint identity vertex. -/
def normalOpenPositionWord {n : ℕ} (m L θ : ℝ) (a e : UnitAddCircle) (u : Fin n → UnitVector OSFourSpace)
    (p : Fin (n+1) → OSFourSpace) (x : Fin n → UnitAddCircle) : DiracMatrix :=
  normalOrderedWord (fun i => normalQuotientKernel m L θ (p i)
    (Fin.cons (α := fun _ => UnitAddCircle) (normalAnchoredVertices e x 0-a) (normalEndpointDifferences e x) i) * normalOpenVertex u i)

theorem normal_quotient_open_measurable {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ) (δ : UnitAddCircle)
    (u : Fin n → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) : Measurable (normalQuotientOpenWord m L θ δ u p) := by
  have h (i : Fin (n+1)) : Measurable (fun t : Fin n → UnitAddCircle =>
      Fin.cons (α := fun _ => UnitAddCircle) (δ-∑ j, t j) t i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]; fun_prop
    · simp only [Fin.cons_succ]; exact measurable_pi_apply j
  exact normal_ordered_measurable _ (fun i => ((normal_quotient_kernel_measurable hm hL θ (p i)).comp (h i)).mul_const (normalOpenVertex u i))

theorem normal_open_word_lift {n : ℕ} (m L θ δ : ℝ) (u : Fin n → UnitVector OSFourSpace)
    (p : Fin (n+1) → OSFourSpace) (t : Fin n → ℝ) :
    normalQuotientOpenWord m L θ (δ:UnitAddCircle) u p (fun j => (t j : UnitAddCircle)) = normalCircleOpenWord m L θ δ u p t := by
  let q := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1:ℝ))
  have he (i : Fin (n+1)) : Fin.cons (α := fun _ => UnitAddCircle) (q δ-∑ j, q (t j)) (fun j => q (t j)) i =
      q (normalOpenIncrements δ t i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change q δ-∑ j, q (t j) = q (δ-∑ j, t j)
      exact (congrArg (q δ-·) (map_sum q t Finset.univ).symm).trans (map_sub q _ _).symm
    · rfl
  change normalOrderedWord (fun i => normalQuotientKernel m L θ (p i)
    (Fin.cons (α := fun _ => UnitAddCircle) (q δ-∑ j, q (t j)) (fun j => q (t j)) i) * normalOpenVertex u i) = _
  simp_rw [he]
  rfl

theorem normal_open_position_integral {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ z z' : ℝ)
    (hz : z ∈ Icc 0 L) (hz' : z' ∈ Icc 0 L) (u : Fin n → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) :
    L^n • (∫ x, normalOpenPositionWord m L θ ((z/L:ℝ):UnitAddCircle) ((z'/L:ℝ):UnitAddCircle) u p x) =
      ∑' w : ℤ, normalAngularPhase θ ((z'-z)/L+(w:ℝ)) • ∫ x, normalOpenDiracWord normalCoverGamma5 m (z'-z+(w:ℝ)*L) u p x := by
  let a : UnitAddCircle := ((z/L:ℝ):UnitAddCircle)
  let e : UnitAddCircle := ((z'/L:ℝ):UnitAddCircle)
  let δ := (z'-z)/L
  let H := normalQuotientOpenWord m L θ (δ:UnitAddCircle) u p
  have hδ : (δ:UnitAddCircle) = e-a := by
    dsimp [δ,e,a]
    rw [sub_div,AddCircle.coe_sub]
  have hpos (x : Fin n → UnitAddCircle) : normalOpenPositionWord m L θ a e u p x = H (normalEndpointDifferences e x) := by
    have h := normal_circle_closing_increment (normalAnchoredVertices e x)
    change -(∑ j, normalEndpointDifferences e x j) = normalAnchoredVertices e x 0-normalAnchoredVertices e x (Fin.last n) at h
    have he : normalAnchoredVertices e x (Fin.last n) = e := Fin.snoc_last ..
    rw [he] at h
    have hd : (δ:UnitAddCircle)-∑ j, normalEndpointDifferences e x j = normalAnchoredVertices e x 0-a := by
      rw [hδ,sub_eq_add_neg (e-a),h]; abel
    simp only [normalOpenPositionWord,H,normalQuotientOpenWord,hd]
  have hmH := normal_quotient_open_measurable hm hL θ (δ:UnitAddCircle) u p
  have hv := normal_endpoint_differences_preserving (n := n) e
  have ht := normal_circle_unit_cell n
  have h1 : (∫ x, H (normalEndpointDifferences e x)) = ∫ t, H t := by
    rw [←integral_map hv.measurable.aemeasurable hmH.aestronglyMeasurable,hv.map_eq]
  have h2 : (∫ t in normalUnitCell n, H (fun j => (t j : UnitAddCircle))) = ∫ t, H t := by
    rw [←integral_map ht.measurable.aemeasurable hmH.aestronglyMeasurable,ht.map_eq]
  change L^n • (∫ x, normalOpenPositionWord m L θ a e u p x) = _
  simp_rw [hpos]
  rw [h1,←h2]
  change L^n • (∫ t in normalUnitCell n, normalQuotientOpenWord m L θ (δ:UnitAddCircle) u p (fun j => (t j : UnitAddCircle))) = _
  simp_rw [normal_open_word_lift]
  exact normal_circle_open_integral hm hL θ z z' hz hz' u p

end UV
