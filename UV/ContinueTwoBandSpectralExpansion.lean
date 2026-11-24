import UV.ContinueTwoBandSpectralDifferences

/-! Adaptive expansion of the complete marked onsite interval. Large transfers
are kept as translations with their exact denominator. Small and zero transfers
insert another onsite factor at every possible position. The coefficient
estimate supplies one inverse-frequency weight for each end independently. -/

noncomputable section
open MeasureTheory Complex Filter
open scoped Topology

namespace UV.SectorPlane

abbrev HoppingTerm := ℂ × List ℝ

def hoppingEval (a : ℝ) (P : List HoppingTerm) (s : ℝ) : ℂ :=
  (P.map (fun t => t.1*hoppingWord a t.2 s)).sum

def hoppingExpandTerm (ν : ℝ) (t : HoppingTerm) : List HoppingTerm :=
  if 1 < |ν| then [(t.1/(I*ν),t.2.map (·+ν)),(-t.1/(I*ν),t.2)]
  else (hoppingInsert ν t.2).map (fun B => (t.1,B))

def hoppingExpand (ν : ℝ) (P : List HoppingTerm) := P.flatMap (hoppingExpandTerm ν)

/-- Marks in the list are applied successively, starting with the first. -/
def hoppingMarks : List ℝ → (ℝ → ℂ) → (ℝ → ℂ)
  | [], f => f
  | ν::V, f => hoppingMarks V (hoppingDifference ν f)

def hoppingExpansion : List ℝ → List HoppingTerm → List HoppingTerm
  | [], P => P
  | ν::V, P => hoppingExpansion V (hoppingExpand ν P)

private theorem eval_diff {a : ℝ} (ha : a ≠ 0) (P : List HoppingTerm) :
    Differentiable ℝ (hoppingEval a P) := by
  induction P with
  | nil => exact differentiable_const _
  | cons t P ih =>
    intro x
    exact ((hopping_word_differentiable ha _ x).const_mul _).add (ih x)

private theorem eval_append (a s : ℝ) (P Q : List HoppingTerm) :
    hoppingEval a (P++Q) s = hoppingEval a P s + hoppingEval a Q s := by simp [hoppingEval]

private theorem difference_add (ν : ℝ) {f g : ℝ → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (s : ℝ) : hoppingDifference ν (fun x => f x+g x) s =
    hoppingDifference ν f s + hoppingDifference ν g s := by
  by_cases h : ν=0
  · simp [hoppingDifference,h,deriv_fun_add (hf s) (hg s),add_div]
  · simp only [hoppingDifference,if_neg h,div_eq_mul_inv]; ring

private theorem difference_mul (ν : ℝ) (c : ℂ) {f : ℝ → ℂ} (hf : Differentiable ℝ f) (s : ℝ) :
    hoppingDifference ν (fun x => c*f x) s = c*hoppingDifference ν f s := by
  by_cases h : ν=0
  · simp [hoppingDifference,h,deriv_const_mul c (hf s),div_eq_mul_inv,mul_assoc]
  · simp only [hoppingDifference,if_neg h,div_eq_mul_inv]; ring

theorem hopping_eval_step {a : ℝ} (ha : a ≠ 0) (ν : ℝ) (P : List HoppingTerm) :
    hoppingDifference ν (hoppingEval a P) = hoppingEval a (hoppingExpand ν P) := by
  funext s
  induction P with
  | nil => by_cases h : ν=0 <;> simp [hoppingDifference,h,hoppingExpand,hoppingEval,
      show hoppingEval a [] = fun _ => 0 by rfl]
  | cons t P ih =>
    change hoppingDifference ν (fun x => t.1*hoppingWord a t.2 x + hoppingEval a P x) s = _
    rw [difference_add ν ((hopping_word_differentiable ha _).const_mul _) (eval_diff ha _) s,
      difference_mul ν _ (hopping_word_differentiable ha _) s,ih]
    change _ = hoppingEval a (hoppingExpandTerm ν t ++ hoppingExpand ν P) s
    rw [eval_append]
    congr 1
    by_cases h : 1 < |ν|
    · have hn := abs_pos.mp (zero_lt_one.trans h)
      rw [hoppingDifference,if_neg hn,hopping_word_translate a ν s,
        hoppingExpandTerm,if_pos h]
      simp [hoppingEval,div_eq_mul_inv]
      ring
    · rw [hopping_word_difference ha,hoppingExpandTerm,if_neg h]
      induction hoppingInsert ν t.2 with
      | nil => simp [hoppingEval]
      | cons _ _ hi =>
        simpa [hoppingEval,List.map_map,Function.comp_def,mul_add] using hi

/-- The adaptive words evaluate to the exact repeated difference at every frequency. -/
theorem hopping_expansion_exact {a : ℝ} (ha : a ≠ 0) (V : List ℝ) (P : List HoppingTerm) :
    hoppingMarks V (hoppingEval a P) = hoppingEval a (hoppingExpansion V P) := by
  induction V generalizing P with
  | nil => rfl
  | cons ν V ih => rw [hoppingMarks,hoppingExpansion,hopping_eval_step ha,ih]

def hoppingCost (P : List HoppingTerm) : ℝ := (P.map (fun t => ‖t.1‖)).sum

def hoppingWeight (V : List ℝ) : ℝ := (V.map (fun ν => (1+|ν|)⁻¹)).prod

private theorem insert_count (ν : ℝ) (B : List ℝ) : (hoppingInsert ν B).length = B.length := by
  induction B with
  | nil => rfl
  | cons _ _ ih => simp [hoppingInsert,ih]

private theorem insert_length (ν : ℝ) (B D : List ℝ) (h : D ∈ hoppingInsert ν B) :
    D.length = B.length+1 := by
  induction B generalizing D with
  | nil => simp [hoppingInsert] at h
  | cons b B ih =>
    simp only [hoppingInsert,List.mem_cons,List.mem_map] at h
    rcases h with rfl | ⟨E,hE,rfl⟩
    · simp
    · simp [ih E hE]

def HoppingDegree (K : ℕ) (P : List HoppingTerm) : Prop :=
  ∀ t ∈ P, 1 ≤ t.2.length ∧ t.2.length ≤ K

theorem hopping_expand_degree {K : ℕ} {P : List HoppingTerm} (hP : HoppingDegree K P) (ν : ℝ) :
    HoppingDegree (K+1) (hoppingExpand ν P) := by
  intro t ht
  obtain ⟨u,hu,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨h₁,h₂⟩ := hP u hu
  by_cases h : 1 < |ν|
  · simp [hoppingExpandTerm,h] at ht
    rcases ht with rfl | rfl <;> simp_all <;> omega
  · simp only [hoppingExpandTerm,if_neg h,List.mem_map] at ht
    obtain ⟨B,hB,rfl⟩ := ht
    simp only [insert_length ν _ _ hB]
    omega

private theorem cost_append (P Q : List HoppingTerm) : hoppingCost (P++Q) = hoppingCost P+hoppingCost Q := by
  simp [hoppingCost]

private theorem expand_term_cost {K : ℕ} {t : HoppingTerm} (ht : t.2.length ≤ K) (ν : ℝ) :
    hoppingCost (hoppingExpandTerm ν t) ≤ (4*(K+1:ℕ):ℝ)*(1+|ν|)⁻¹*‖t.1‖ := by
  have hpos : 0 < 1+|ν| := by positivity
  by_cases h : 1 < |ν|
  · have hν : 0 < |ν| := by linarith
    simp only [hoppingExpandTerm,if_pos h,hoppingCost,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,norm_div,norm_neg,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      add_zero]
    push_cast
    rw [show (4*((K:ℝ)+1))*(1+|ν|)⁻¹*‖t.1‖ = (4*((K:ℝ)+1)*‖t.1‖)/(1+|ν|) by ring]
    rw [le_div_iff₀ hpos,←add_div,mul_comm _ (1+|ν|),←mul_div_assoc,div_le_iff₀ hν]
    have hK : 0 ≤ (K:ℝ)*‖t.1‖*|ν| := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h.le (norm_nonneg t.1)]
  · simp only [hoppingExpandTerm,if_neg h,hoppingCost,List.map_map,Function.comp_def,List.map_const',
      List.sum_replicate,insert_count,nsmul_eq_mul]
    push_cast
    have hn : (t.2.length:ℝ) ≤ K := by exact_mod_cast ht
    have hk : 0 ≤ (K:ℝ) := by positivity
    have hc : (t.2.length:ℝ) ≤ 4*((K:ℝ)+1)*(1+|ν|)⁻¹ := by
      rw [←div_eq_mul_inv,le_div_iff₀ hpos]
      exact (mul_le_mul_of_nonneg_left (by linarith [le_of_not_gt h] : 1+|ν| ≤ 2) (by positivity)).trans
        (by linarith)
    exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

theorem hopping_expand_cost {K : ℕ} {P : List HoppingTerm} (hP : HoppingDegree K P) (ν : ℝ) :
    hoppingCost (hoppingExpand ν P) ≤ (4*(K+1:ℕ):ℝ)*(1+|ν|)⁻¹*hoppingCost P := by
  induction P with
  | nil => simp [hoppingCost,hoppingExpand]
  | cons t P ih =>
    change hoppingCost (hoppingExpandTerm ν t ++ hoppingExpand ν P) ≤ _
    rw [cost_append]
    have hC := expand_term_cost (hP t (List.mem_cons_self)).2 ν
    have hr := ih (fun p hp => hP p (List.mem_cons_of_mem t hp))
    simpa only [hoppingCost,List.map_cons,List.sum_cons,mul_add] using add_le_add hC hr

/-- The finite cost depends only on the number of marks and initial degree. -/
def hoppingCountFactor : ℕ → ℕ → ℝ
  | _, 0 => 1
  | K, d+1 => (4*(K+1:ℕ):ℝ)*hoppingCountFactor (K+1) d

theorem hopping_count_nonneg (K d : ℕ) : 0 ≤ hoppingCountFactor K d := by
  induction d generalizing K with
  | zero => simp [hoppingCountFactor]
  | succ _ ih => exact mul_nonneg (by positivity) (ih _)

theorem hopping_weight_nonneg (V : List ℝ) : 0 ≤ hoppingWeight V := by
  induction V with
  | nil => simp [hoppingWeight]
  | cons _ _ ih => exact mul_nonneg (by positivity) ih

theorem hopping_expansion_cost {K : ℕ} {P : List HoppingTerm} (hP : HoppingDegree K P) (V : List ℝ) :
    HoppingDegree (K+V.length) (hoppingExpansion V P) ∧
      hoppingCost (hoppingExpansion V P) ≤ hoppingCountFactor K V.length*hoppingWeight V*hoppingCost P := by
  induction V generalizing K P with
  | nil => simp [hoppingExpansion,hoppingCountFactor,hoppingWeight,hP]
  | cons ν V ih =>
    have h := ih (hopping_expand_degree hP ν)
    refine ⟨by simpa [hoppingExpansion,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.1,?_⟩
    have hw := hopping_weight_nonneg V
    calc
      _ ≤ _ := h.2
      _ ≤ _ := mul_le_mul_of_nonneg_left (hopping_expand_cost hP ν) (mul_nonneg (hopping_count_nonneg _ _) hw)
      _ = _ := by simp only [hoppingCountFactor,hoppingWeight,List.length_cons,List.map_cons,List.prod_cons]; ring

end UV.SectorPlane
