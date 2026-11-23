import UV.ContinueMarkedPhotonWick
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The true second Fréchet derivative of a common multilinear source
marks an ordered pair of distinct physical ports. Every Wick contraction
of the remaining slots acquires an explicit parent matching on sewing.
Factoring out the restored covariance gives the signed Hessian marginal. -/

noncomputable section
open MeasureTheory Set Filter Classical
open scoped BigOperators

namespace UV.MarkedPhoton

variable {P : Type*}

abbrev WickRemainder (e : Fin 2 ↪ P) := {j : P // j ∉ range e}

/-- The Hessian before the two probes are sewn. Each ordered injection
of the two marks picks two different ports and replaces only their fields. -/
theorem distinct_port_hessian {F : Type*} [Fintype P] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ContinuousMultilinearMap ℝ (fun _ : P => F) ℝ) (a : P → F) (w : Fin 2 → P → F) :
    iteratedFDeriv ℝ 2 L a w = ∑ e : Fin 2 ↪ P,
      L (fun j => if h : j ∈ range e then w (e.toEquivRange.symm ⟨j,h⟩) j else a j) := by
  classical
  rw [L.iteratedFDeriv_eq,ContinuousMultilinearMap.iteratedFDeriv]
  simp [ContinuousMultilinearMap.sum_apply]

/-- Given the ordered Hessian marks and any complete matching of the
remaining ports, make the physical new edge the first edge. -/
def restoreWickEdge {n : ℕ} (e : Fin 2 ↪ P) (q : WickRemainder e ≃ Fin n × Fin 2) :
    P ≃ Fin (n+1) × Fin 2 where
  toFun j := if h : j ∈ range e then (0,e.toEquivRange.symm ⟨j,h⟩) else
    ((q ⟨j,h⟩).1.succ,(q ⟨j,h⟩).2)
  invFun t := Fin.cases (e t.2) (fun j => (q.symm (j,t.2)).val) t.1
  left_inv j := by
    dsimp only
    split_ifs with h
    · change e (e.toEquivRange.symm ⟨j,h⟩) = j
      exact congrArg Subtype.val (e.toEquivRange.apply_symm_apply ⟨j,h⟩)
    · simp
  right_inv t := by
    rcases t with ⟨i,side⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · have hn : (q.symm (j,side)).val ∉ range e := (q.symm (j,side)).property
      simp [hn]

@[simp] theorem restoreWickEdge_mark {n : ℕ} (e : Fin 2 ↪ P) (q : WickRemainder e ≃ Fin n × Fin 2) (s : Fin 2) :
    restoreWickEdge e q (e s) = (0,s) := by
  classical
  dsimp only [restoreWickEdge,Equiv.coe_fn_mk]
  rw [dif_pos (Set.mem_range_self s)]
  exact congrArg (fun t => ((0:Fin (n+1)),t)) (e.toEquivRange.symm_apply_apply s)

@[simp] theorem restoreWickEdge_other {n : ℕ} (e : Fin 2 ↪ P) (q : WickRemainder e ≃ Fin n × Fin 2)
    (i : WickRemainder e) : restoreWickEdge e q i.val = ((q i).1.succ,(q i).2) := by
  classical
  dsimp only [restoreWickEdge,Equiv.coe_fn_mk]
  rw [dif_neg i.property]

variable {X : Type*} [MeasurableSpace X]

def openWickHessian {n : ℕ} (e : Fin 2 ↪ P) (q : WickRemainder e ≃ Fin n × Fin 2)
    (kernel : (P → X) → ℝ) (v : Fin 2 → X → X) (covariance : X → ℝ) (x : X) (y : Fin n → X) : ℝ :=
  kernel (fun j => if h : j ∈ range e then v (e.toEquivRange.symm ⟨j,h⟩) x else
    v (q ⟨j,h⟩).2 (y (q ⟨j,h⟩).1)) * ∏ j, covariance (y j)

omit [MeasurableSpace X] in
/-- Sewing restores exactly the removed covariance and no extra port or
weight. Signed contractions can mix momenta arbitrarily in the kernel. -/
theorem restore_parent_identity {n : ℕ} (e : Fin 2 ↪ P) (q : WickRemainder e ≃ Fin n × Fin 2)
    (kernel : (P → X) → ℝ) (v : Fin 2 → X → X) (covariance : X → ℝ) (x : X) (y : Fin n → X) :
    wickParent (restoreWickEdge e q) kernel v covariance (Fin.cons (α := fun _ => X) x y) =
      covariance x * openWickHessian e q kernel v covariance x y := by
  classical
  have hh : (fun j => v ((restoreWickEdge e q j).2) (Fin.cons (α := fun _ => X) x y (restoreWickEdge e q j).1)) =
      fun j => if h : j ∈ range e then v (e.toEquivRange.symm ⟨j,h⟩) x else v (q ⟨j,h⟩).2 (y (q ⟨j,h⟩).1) := by
    funext j
    by_cases hj : j ∈ range e
    · obtain ⟨s,rfl⟩ := hj
      rw [restoreWickEdge_mark,dif_pos (Set.mem_range_self s),Fin.cons_zero]
      exact congrArg (fun t => v t x) (e.toEquivRange.symm_apply_apply s).symm
    · rw [dif_neg hj,show restoreWickEdge e q j = _ from restoreWickEdge_other e q ⟨j,hj⟩,Fin.cons_succ]
  rw [wickParent,openWickHessian,hh,Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  ring

theorem traced_hessian_mark_integrable {n : ℕ} (e : Fin 2 ↪ P) (q : WickRemainder e ≃ Fin n × Fin 2)
    (kernel : (P → X) → ℝ) (v : Fin 2 → X → X) (covariance : X → ℝ)
    (μ : Measure X) [SigmaFinite μ]
    (hParent : Integrable (wickParent (restoreWickEdge e q) kernel v covariance) (Measure.pi (fun _ => μ))) :
    let M := fun x => covariance x * ∫ y, openWickHessian e q kernel v covariance x y ∂Measure.pi (fun _ => μ)
    Integrable M μ ∧ (∫ x, ‖M x‖ ∂μ) ≤ ∫ p, ‖wickParent (restoreWickEdge e q) kernel v covariance p‖ ∂Measure.pi (fun _ => μ) := by
  let pairing := restoreWickEdge e q
  have h := marked_wick_parent_sewing pairing kernel v covariance μ (e 0) hParent
  have he (x y) : markedPairLift pairing (e 0) (x,y) = Fin.cons (α := fun _ => X) x y := by
    change (pairing (e 0)).1.insertNth (α := fun _ => X) x y = _
    rw [show (pairing (e 0)).1=0 by simp [pairing]]
    exact Fin.insertNth_zero' x y
  dsimp only at h
  simp_rw [he] at h
  dsimp only [pairing] at h
  simp_rw [restore_parent_identity,integral_const_mul] at h
  exact h

/-- A finite signed interaction coefficient can contain different photon
degrees and different complete pairings. Their actual traced Hessian
marginals are jointly controlled by the sum of the corresponding parent
absolute integrals, once per ordered mark. -/
theorem measured_hessian_sewing_absolute {J : Type*} (s : Finset J) (n : J → ℕ)
    (Ports : J → Type*) (e : ∀ j, Fin 2 ↪ Ports j)
    (q : ∀ j, WickRemainder (e j) ≃ Fin (n j) × Fin 2)
    (kernel : ∀ j, (Ports j → X) → ℝ) (v : Fin 2 → X → X) (covariance : X → ℝ)
    (μ : Measure X) [SigmaFinite μ]
    (hParent : ∀ j ∈ s, Integrable (wickParent (restoreWickEdge (e j) (q j)) (kernel j) v covariance)
      (Measure.pi (fun _ => μ))) :
    let M := fun j x => covariance x * ∫ y, openWickHessian (e j) (q j) (kernel j) v covariance x y ∂Measure.pi (fun _ => μ)
    Integrable (fun x => ∑ j ∈ s, M j x) μ ∧
      (∫ x, ‖∑ j ∈ s, M j x‖ ∂μ) ≤ ∑ j ∈ s,
        ∫ p, ‖wickParent (restoreWickEdge (e j) (q j)) (kernel j) v covariance p‖ ∂Measure.pi (fun _ => μ) := by
  let M := fun j x => covariance x * ∫ y, openWickHessian (e j) (q j) (kernel j) v covariance x y ∂Measure.pi (fun _ => μ)
  have h j (hj : j ∈ s) := traced_hessian_mark_integrable (e j) (q j) (kernel j) v covariance μ (hParent j hj)
  have hi j (hj : j ∈ s) : Integrable (M j) μ := (h j hj).1
  have hs := integrable_finset_sum s hi
  refine ⟨hs,?_⟩
  calc
    (∫ x, ‖∑ j ∈ s, M j x‖ ∂μ) ≤ ∫ x, ∑ j ∈ s, ‖M j x‖ ∂μ :=
      integral_mono hs.norm (integrable_finset_sum s fun j hj => (hi j hj).norm) (fun x => norm_sum_le s _)
    _ = _ := integral_finset_sum s fun j hj => (hi j hj).norm
    _ ≤ _ := Finset.sum_le_sum fun j hj => (h j hj).2

end UV.MarkedPhoton
