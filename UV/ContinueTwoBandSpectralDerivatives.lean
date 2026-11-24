import UV.ContinueTwoBandSpectralMarkedBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Powers of the signed duration introduced by soft basepoint subtractions
are charged-frequency derivatives. Every derivative is an extra zero-frequency
interval mark, up to its exact unit imaginary phase. -/

noncomputable section
open MeasureTheory Complex

namespace UV.SectorPlane

private theorem marks_append (V W : List ℝ) (f : ℝ → ℂ) :
    hoppingMarks (V++W) f = hoppingMarks W (hoppingMarks V f) := by
  induction V generalizing f with
  | nil => rfl
  | cons ν V ih => exact ih (hoppingDifference ν f)

private theorem marks_diff {a : ℝ} (ha : a ≠ 0) (V : List ℝ) (b : ℝ) :
    Differentiable ℝ (hoppingMarks V (fun s => hoppingInterval a (s+b))) := by
  let Q : List HoppingTerm := [(1,[b])]
  have he : hoppingEval a Q = fun s => hoppingInterval a (s+b) := by funext; simp [Q,hoppingEval,hoppingWord]
  rw [←he,hopping_expansion_exact ha]
  generalize hoppingExpansion V Q = P
  induction P with
  | nil => exact differentiable_const _
  | cons t P ih =>
    intro x
    exact ((hopping_word_differentiable ha _ x).const_mul _).add (ih x)

theorem hopping_marked_iterated_deriv {a : ℝ} (ha : a ≠ 0) (V : List ℝ) (b : ℝ) (n : ℕ) :
    iteratedDeriv n (hoppingMarks V (fun s => hoppingInterval a (s+b))) =
      fun s => I^n*hoppingMarks (V++List.replicate n 0) (fun s => hoppingInterval a (s+b)) s := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    let f := fun s => hoppingInterval a (s+b)
    let G := hoppingMarks (V++List.replicate n 0) f
    have hd : Differentiable ℝ G := marks_diff ha _ b
    rw [iteratedDeriv_succ,ih,List.replicate_add,List.replicate_one,←List.append_assoc,marks_append _ [0]]
    funext s
    change deriv (fun x => I^n*G x) s = I^(n+1)*hoppingDifference 0 G s
    rw [deriv_const_mul _ (hd s)]
    rw [hoppingDifference,if_pos (rfl : (0:ℝ)=0),pow_succ]
    field_simp

private theorem weight_append_zeros (V : List ℝ) (n : ℕ) :
    hoppingWeight (V++List.replicate n 0) = hoppingWeight V := by simp [hoppingWeight]

/-- The absolute two-interval estimate persists under every fixed number
of derivatives contributed by the spatial and transverse soft subtractions. -/
theorem hopping_marked_derivative_pair {m a c : ℝ} (hm : 0 < m) (ha : |a|=m) (hc : |c|=m)
    (b d : ℝ) (V W : List ℝ) (n r : ℕ) :
    let F := iteratedDeriv n (hoppingMarks V (fun x => hoppingInterval a (x+b)))
    let G := iteratedDeriv r (hoppingMarks W (fun x => hoppingInterval c (x+d)))
    Integrable (fun s => F s*G s) ∧
      (∫ s, ‖F s*G s‖) ≤ (Real.pi/m)*
        (hoppingIntervalConstant m (V.length+n)*hoppingWeight V)*
        (hoppingIntervalConstant m (W.length+r)*hoppingWeight W) := by
  dsimp only
  rw [hopping_marked_iterated_deriv (abs_pos.mp (ha.symm ▸ hm)),
    hopping_marked_iterated_deriv (abs_pos.mp (hc.symm ▸ hm))]
  let F := hoppingMarks (V++List.replicate n 0) (fun x => hoppingInterval a (x+b))
  let G := hoppingMarks (W++List.replicate r 0) (fun x => hoppingInterval c (x+d))
  have h := hopping_marked_interval_pair hm ha hc b d (V++List.replicate n 0) (W++List.replicate r 0)
  change Integrable (fun s => I^n*F s*(I^r*G s)) ∧ (∫ s, ‖I^n*F s*(I^r*G s)‖) ≤ _
  have he (s : ℝ) : I^n*F s*(I^r*G s) = (I^n*I^r)*(F s*G s) := by ring
  simp_rw [he]
  refine ⟨h.1.const_mul _,?_⟩
  simpa only [norm_mul,norm_pow,norm_I,one_pow,one_mul,List.length_append,List.length_replicate,
    weight_append_zeros,F,G] using h.2

theorem hopping_marked_derivative_sup {m a : ℝ} (hm : 0<m) (ha : |a|=m) (b : ℝ)
    (V : List ℝ) (n : ℕ) (s : ℝ) :
    ‖iteratedDeriv n (hoppingMarks V (fun x => hoppingInterval a (x+b))) s‖ ≤
      m⁻¹*(hoppingIntervalConstant m (V.length+n)*hoppingWeight V) := by
  rw [hopping_marked_iterated_deriv (abs_pos.mp (ha.symm ▸ hm)),norm_mul,norm_pow,norm_I,one_pow,one_mul]
  have h := hopping_marked_interval_sup hm ha b (V++List.replicate n 0) s
  rw [List.length_append,List.length_replicate,weight_append_zeros,mul_assoc] at h
  exact h

theorem hopping_marked_derivative_continuous {a : ℝ} (ha : a ≠ 0) (b : ℝ) (V : List ℝ) (n : ℕ) :
    Continuous (iteratedDeriv n (hoppingMarks V (fun x => hoppingInterval a (x+b)))) := by
  rw [hopping_marked_iterated_deriv ha]
  exact continuous_const.mul (marks_diff ha _ b).continuous

end UV.SectorPlane
