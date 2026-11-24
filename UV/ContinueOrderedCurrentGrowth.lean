import UV.ContinueOrderedCurrentReturn
import UV.ContinueOrderedHopTrace
import UV.ContinueOrderedEnvelopeSewing

/-! Uniform polynomial budgets for the charged paths appearing in all
edge incidences and the two external marks, on the original return variables.
Their absolute signed trace weights are summable in each vertex's hop count. -/

noncomputable section

open MeasureTheory Finset

namespace UV.SectorPlane

def orderedVertexCost {n : ℕ} (d : Fin n → OrderedHopStep) : ℝ :=
  9*(1+(n:ℝ))*(1+orderedHopPathLength d)^2

theorem orderedVertexCost_one_le {n : ℕ} (d : Fin n → OrderedHopStep) : 1 ≤ orderedVertexCost d := by
  have h := orderedHop_path_length_nonneg d
  unfold orderedVertexCost
  have h1 : 1 ≤ (1+orderedHopPathLength d)^2 := one_le_pow₀ (by linarith)
  nlinarith [le_mul_of_one_le_right (show 0 ≤ 9*(1+(n:ℝ)) by positivity) h1, Nat.cast_nonneg (α := ℝ) n]

theorem orderedVertexCost_pathCost {n : ℕ} (k : OrderedPhotonKind) (d : Fin n → OrderedHopStep) :
    k.pathCost (OrderedTwoBandPath.returnPath d) ≤ orderedVertexCost d := by
  cases k <;> simp only [OrderedPhotonKind.pathCost,OrderedTwoBandPath.return_path_length,orderedVertexCost,
    show (OrderedTwoBandPath.returnPath d).hops = n+1 from rfl,Nat.cast_add,Nat.cast_one]
  · rw [show (9:ℝ)*(1+orderedHopPathLength d)^2 = 9*1*(1+orderedHopPathLength d)^2 by ring]
    gcongr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem orderedVertexCost_external {n : ℕ} (d : Fin n → OrderedHopStep) :
    3*(1+(OrderedTwoBandPath.returnPath d).length)^2 ≤ orderedVertexCost d := by
  rw [OrderedTwoBandPath.return_path_length,orderedVertexCost]
  gcongr
  linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem orderedVertexCost_le_prod {V : Type*} [Fintype V] {N : V → ℕ}
    (d : (v : V) → Fin (N v) → OrderedHopStep) (v : V) :
    orderedVertexCost (d v) ≤ ∏ w, orderedVertexCost (d w) := by
  classical
  rw [←mul_prod_erase univ (fun w => orderedVertexCost (d w)) (mem_univ v)]
  apply le_mul_of_one_le_right (zero_le_one.trans (orderedVertexCost_one_le _))
  simpa only [prod_const_one] using prod_le_prod (s := univ.erase v)
    (fun _ _ => (zero_le_one : (0:ℝ) ≤ 1)) (fun w _ => orderedVertexCost_one_le (d w))

variable {E V : Type*} [Fintype E] [Fintype V]

theorem ordered_edges_growth (src dst : E → V) (kind : E → OrderedPhotonKind)
    (N : V → ℕ) (d : (v : V) → Fin (N v) → OrderedHopStep) :
    (∏ e, (kind e).pathCost (OrderedTwoBandPath.returnPath (d (src e))) *
      (kind e).pathCost (OrderedTwoBandPath.returnPath (d (dst e)))) ≤
      ∏ v, orderedVertexCost (d v) ^ (2*Fintype.card E) := by
  let T := ∏ w, orderedVertexCost (d w)
  have hT : 0 ≤ T := prod_nonneg fun _ _ => zero_le_one.trans (orderedVertexCost_one_le _)
  have he (e : E) (v : V) : (kind e).pathCost (OrderedTwoBandPath.returnPath (d v)) ≤ T :=
    (orderedVertexCost_pathCost _ _).trans (orderedVertexCost_le_prod d v)
  calc
    _ ≤ ∏ _e : E, T^2 := prod_le_prod (fun e _ => mul_nonneg ((kind e).pathCost_nonneg _) ((kind e).pathCost_nonneg _))
      (fun e _ => (mul_le_mul (he e _) (he e _) ((kind e).pathCost_nonneg _) hT).trans_eq (sq T).symm)
    _ = _ := by simp only [prod_const,card_univ,←pow_mul,←prod_pow,T]

theorem ordered_external_edges_growth (src dst : E → V) (kind : E → OrderedPhotonKind)
    (N : V → ℕ) (d : (v : V) → Fin (N v) → OrderedHopStep) (s t : V) :
    ((3*(1+(OrderedTwoBandPath.returnPath (d s)).length)^2) *
      (3*(1+(OrderedTwoBandPath.returnPath (d t)).length)^2)) *
      (∏ e, (kind e).pathCost (OrderedTwoBandPath.returnPath (d (src e))) *
        (kind e).pathCost (OrderedTwoBandPath.returnPath (d (dst e)))) ≤
      ∏ v, orderedVertexCost (d v) ^ (2*Fintype.card E+2) := by
  let T := ∏ w, orderedVertexCost (d w)
  have hT : 0 ≤ T := prod_nonneg fun _ _ => zero_le_one.trans (orderedVertexCost_one_le _)
  have h (v : V) : 3*(1+(OrderedTwoBandPath.returnPath (d v)).length)^2 ≤ T :=
    (orderedVertexCost_external _).trans (orderedVertexCost_le_prod d v)
  have hprod := ordered_edges_growth src dst kind N d
  apply (mul_le_mul (mul_le_mul (h s) (h t) (by positivity) hT) hprod
    (prod_nonneg fun e _ => mul_nonneg ((kind e).pathCost_nonneg _) ((kind e).pathCost_nonneg _)) (mul_nonneg hT hT)).trans_eq
  simp only [T,←prod_pow,←sq,pow_add,mul_comm,prod_mul_distrib]

theorem orderedVertexCost_log_summable {m σ g : ℝ} (hσ : 0 < σ) (hg : 2*|g| < m)
    (r : ℕ) (φ : (n : ℕ) → OrderedHopPhases n) (hφ : ∀ n j s, Measurable (φ n j s)) :
    (∀ n, Integrable (fun d => (orderedVertexCost d)^r * ‖orderedHopLogWord m σ g (φ n) d‖)) ∧
      Summable (fun n => ∫ d, (orderedVertexCost d)^r * ‖orderedHopLogWord m σ g (φ n) d‖) := by
  let M := fun (n : ℕ) (d : Fin n → OrderedHopStep) => ((orderedVertexCost d)^r : ℂ)
  have hnorm (n : ℕ) (d : Fin n → OrderedHopStep) : ‖M n d‖ = (orderedVertexCost d)^r := by
    have hc := zero_le_one.trans (orderedVertexCost_one_le d)
    simp [M,Real.norm_of_nonneg hc]
  have hm (n : ℕ) : Measurable (M n) := by
    unfold M orderedVertexCost
    fun_prop
  have hb (n : ℕ) (d : Fin n → OrderedHopStep) :
      ‖M n d‖ ≤ 9^r*(1+(n:ℝ))^r*(1+orderedHopPathLength d)^(2*r) := by
    rw [hnorm,orderedVertexCost,mul_pow,mul_pow,pow_mul]
  have h := orderedHop_marked_log_words_summable hσ hg (show 0 ≤ (9:ℝ)^r by positivity)
    r (2*r) φ hφ M hm hb
  exact ⟨fun n => by simpa only [norm_mul,hnorm] using (h.1 n).norm,
    by simpa only [norm_mul,hnorm] using h.2⟩

end UV.SectorPlane
