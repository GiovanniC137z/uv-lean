import UV.ContinueNormalPeriodicIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Integrate the common normal circle coordinate of the actual insertion
positions. The other coordinates are the successive directed increments
around the loop, in the order of the Dirac word. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV

attribute [local instance] Real.fact_zero_lt_one

local instance normalUnitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

def normalCircleDifferences {n : ℕ} (z : Fin (n+1) → UnitAddCircle) (j : Fin n) : UnitAddCircle :=
  z j.succ-z j.castSucc

def normalCircleCoordinates (n : ℕ) : (Fin (n+1) → UnitAddCircle) →+ UnitAddCircle × (Fin n → UnitAddCircle) where
  toFun z := (z 0,normalCircleDifferences z)
  map_zero' := by ext <;> simp [normalCircleDifferences]
  map_add' a b := Prod.ext rfl (funext fun j => by simp [normalCircleDifferences]; abel)

theorem normal_circle_coordinates_preserving (n : ℕ) : MeasurePreserving (normalCircleCoordinates n) := by
  let F := normalCircleCoordinates n
  have hF : Continuous F := by
    change Continuous (fun z : Fin (n+1) → UnitAddCircle => (z 0,fun j : Fin n => z j.succ-z j.castSucc))
    fun_prop
  have hs : Function.Surjective F := by
    rintro ⟨c,t⟩
    refine ⟨fun i => c+Fin.partialSum t i,Prod.ext (by simp [F,normalCircleCoordinates]) (funext fun j => ?_)⟩
    change (c+Fin.partialSum t j.succ)-(c+Fin.partialSum t j.castSucc) = t j
    rw [Fin.partialSum_succ]; abel
  let μ := (volume : Measure (Fin (n+1) → UnitAddCircle))
  let ν := (volume : Measure (UnitAddCircle × (Fin n → UnitAddCircle)))
  haveI : IsAddLeftInvariant (μ.map F) := isAddLeftInvariant_map F.toAddHom hF.measurable hs
  haveI : IsProbabilityMeasure (μ.map F) := Measure.isProbabilityMeasure_map hF.measurable.aemeasurable
  haveI : IsAddHaarMeasure ν := Measure.prod.instIsAddHaarMeasure (volume : Measure UnitAddCircle) (volume : Measure (Fin n → UnitAddCircle))
  have h := isAddLeftInvariant_eq_smul (μ.map F) ν
  have hc := congrArg (fun μ' : Measure (UnitAddCircle × (Fin n → UnitAddCircle)) => μ' univ) h
  simp only [measure_univ,Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,mul_one] at hc
  have hscalar : (μ.map F).addHaarScalarFactor ν = 1 := by exact_mod_cast hc.symm
  exact ⟨hF.measurable,by simpa only [hscalar,one_smul] using h⟩

/-- Normalized Haar on all marked vertices pushes forward to normalized
Haar on the directed increments. This includes one insertion. -/
theorem normal_circle_differences_preserving (n : ℕ) : MeasurePreserving (normalCircleDifferences (n := n)) :=
  measurePreserving_snd.comp (normal_circle_coordinates_preserving n)

theorem normal_circle_unit_cell (n : ℕ) :
    MeasurePreserving (fun t : Fin n → ℝ => fun j => (t j : UnitAddCircle)) (volume.restrict (normalUnitCell n)) volume := by
  have h : MeasurePreserving ((↑) : ℝ → UnitAddCircle) (volume.restrict (Ico (0:ℝ) 1)) volume := by
    rw [restrict_Ico_eq_restrict_Ioc]
    simpa only [zero_add] using UnitAddCircle.measurePreserving_mk 0
  simpa only [normalUnitCell,volume_pi,Measure.restrict_pi_pi] using
    measurePreserving_pi (fun _ : Fin n => volume.restrict (Ico (0:ℝ) 1)) (fun _ => (volume : Measure UnitAddCircle)) (fun _ => h)

local instance normalVertexMatrixMeasurable : MeasurableSpace DiracMatrix := borel _
local instance normalVertexMatrixBorel : BorelSpace DiracMatrix := ⟨rfl⟩

def normalQuotientKernel (m L θ : ℝ) (p : OSFourSpace) : UnitAddCircle → DiracMatrix :=
  (normal_circle_kernel_periodic m L θ p).lift

theorem normal_quotient_kernel_measurable {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ) (p : OSFourSpace) :
    Measurable (normalQuotientKernel m L θ p) :=
  QuotientAddGroup.measurable_from_quotient.mpr (normal_circle_kernel_measurable hm hL θ p)

def normalQuotientIncrements {n : ℕ} (t : Fin n → UnitAddCircle) : Fin (n+1) → UnitAddCircle := Fin.cons (-∑ j, t j) t

def normalQuotientTrace {n : ℕ} (m L θ : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace)
    (t : Fin n → UnitAddCircle) : ℂ :=
  (normalOrderedWord (fun i => normalQuotientKernel m L θ (p i) (normalQuotientIncrements t i) * diracSlash (u i).val)).trace

/-- The first propagator goes from the last marked vertex to vertex zero;
the other propagators follow the directed order of the marked vertices. -/
def normalVertexTrace {n : ℕ} (m L θ : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace)
    (z : Fin (n+1) → UnitAddCircle) : ℂ :=
  (normalOrderedWord (fun i => normalQuotientKernel m L θ (p i)
    (Fin.cons (α := fun _ => UnitAddCircle) (z 0-z (Fin.last n)) (normalCircleDifferences z) i) * diracSlash (u i).val)).trace

theorem normal_circle_closing_increment {n : ℕ} (z : Fin (n+1) → UnitAddCircle) :
    -(∑ j, normalCircleDifferences z j) = z 0-z (Fin.last n) := by
  simp only [normalCircleDifferences,Finset.sum_sub_distrib]
  have h := (Fin.sum_univ_succ z).symm.trans (Fin.sum_univ_castSucc z)
  rw [neg_sub,sub_eq_sub_iff_add_eq_add]
  exact h.symm

theorem normal_quotient_trace_measurable {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ)
    (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) : Measurable (normalQuotientTrace m L θ u p) := by
  have h (i : Fin (n+1)) : Measurable (fun t : Fin n → UnitAddCircle => normalQuotientIncrements t i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [normalQuotientIncrements,Fin.cons_zero]; fun_prop
    · simp only [normalQuotientIncrements,Fin.cons_succ]; exact measurable_pi_apply j
  have hP := normal_ordered_measurable _ (fun i => ((normal_quotient_kernel_measurable hm hL θ (p i)).comp (h i)).mul_const (diracSlash (u i).val))
  exact (Matrix.traceLinearMap (Fin 4) ℂ ℂ).toContinuousLinearMap.continuous.measurable.comp hP

theorem normal_circle_trace_lift {n : ℕ} (m L θ : ℝ) (u : Fin (n+1) → UnitVector OSFourSpace)
    (p : Fin (n+1) → OSFourSpace) (t : Fin n → ℝ) :
    normalCircleTrace m L θ u p t = L • normalQuotientTrace m L θ u p (fun j => (t j : UnitAddCircle)) := by
  have he (i : Fin (n+1)) : normalQuotientIncrements (fun j => (t j : UnitAddCircle)) i =
      ((normalOpenIncrements 0 t i : ℝ) : UnitAddCircle) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · let q := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1:ℝ))
      change -(∑ j, q (t j)) = q (0-∑ j, t j)
      calc
        -(∑ j, q (t j)) = -q (∑ j, t j) := congrArg Neg.neg (map_sum q t Finset.univ).symm
        _ = q (-(∑ j, t j)) := (map_neg q _).symm
        _ = q (0-∑ j, t j) := congrArg q (zero_sub _).symm
    · simp only [normalQuotientIncrements,normalOpenIncrements,Fin.cons_succ]
  simp only [normalCircleTrace,normalQuotientTrace,he,normalQuotientKernel,Function.Periodic.lift_coe,Complex.real_smul]

/-- With dz=L dt at each marked vertex, the physical circle trace has
exactly one common-center factor L and n independent increments. -/
theorem normal_periodic_vertex_integral {n : ℕ} {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ)
    (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) :
    L^(n+1) • (∫ z, normalVertexTrace m L θ u p z) = ∑' w : ℤ, ∫ x, normalWindingTrace m L (-θ) w u p x := by
  let H := normalQuotientTrace m L θ u p
  have hmH := normal_quotient_trace_measurable hm hL θ u p
  have hV (z) : normalVertexTrace m L θ u p z = H (normalCircleDifferences z) := by
    simp only [normalVertexTrace,H,normalQuotientTrace,normalQuotientIncrements,normal_circle_closing_increment]
  have hv := normal_circle_differences_preserving n
  have ht := normal_circle_unit_cell n
  have h1 : (∫ z, H (normalCircleDifferences z)) = ∫ t, H t := by
    rw [←integral_map hv.measurable.aemeasurable hmH.aestronglyMeasurable,hv.map_eq]
  have h2 : (∫ t in normalUnitCell n, H (fun j => (t j : UnitAddCircle))) = ∫ t, H t := by
    rw [←integral_map ht.measurable.aemeasurable hmH.aestronglyMeasurable,ht.map_eq]
  rw [←normal_circle_trace_integral hm hL θ u p]
  simp_rw [hV,normal_circle_trace_lift]
  rw [h1,integral_smul,h2,smul_smul,pow_succ]

end UV
