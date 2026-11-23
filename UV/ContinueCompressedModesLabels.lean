import UV.ContinueCompressedModesWords

/-! Finite families of independently polarized source components.
Expansion at fixed electric order sums every assignment to the ordered
photon marks of a fermion cycle. -/

noncomputable section
open Matrix UV.SectorPlane
open scoped Matrix.Norms.L2Operator
namespace UV

variable {κ ι H : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [Fintype H]

theorem compressed_ordered_color_sum {r : ℕ} (A : Fin r → H → DiracMatrix) :
    normalOrderedWord (fun b => ∑ c, A b c) =
      ∑ d : Fin r → H, normalOrderedWord (fun b => A b (d b)) := by
  classical
  induction r with
  | zero => simp [normalOrderedWord]
  | succ r ih =>
    let e := Fin.consEquiv (fun _ : Fin (r+1) => H)
    change (List.ofFn (fun i => ∑ c, A i c)).prod = _
    rw [List.ofFn_succ,List.prod_cons]
    change (∑ c, A 0 c)*normalOrderedWord (fun i => ∑ c, A i.succ c) = _
    rw [ih,Finset.sum_mul,←e.sum_comp,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    dsimp only [normalOrderedWord]
    conv_rhs => rw [List.ofFn_succ,List.prod_cons]
    simp only [e,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ]

def compressedLabelCycle {n : ℕ} (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : κ → OSFourSpace) (u : H → κ → κ → UnitVector OSFourSpace) (W : H → κ → κ → ℂ)
    (v : Fin (n+1) → κ) (d : Fin (n+1) → H) : ℂ :=
  let next := finRotate (n+1)
  (∏ b, compressedIncidence L T p (W (d b)) (v b) (v (next b))) *
    compressedLoopTrace m L T ξ (fun b => u (d b) (v b) (v (next b))) (fun b => p (v b))

theorem compressed_labeled_cycle (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ)
    (p : κ → OSFourSpace) (u : H → κ → κ → UnitVector OSFourSpace) (W : H → κ → κ → ℂ)
    {n : ℕ} (i : κ) (z : Fin n → κ) :
    (compressedArc (compressedBlockFree m ξ p * ∑ c, compressedBlockVertex L T ξ p (u c) (W c)) i i z).trace =
      ∑ d : Fin (n+1) → H, compressedLabelCycle m L T ξ p u W (Fin.cons i z) d := by
  classical
  let v := Fin.cons (α := fun _ => κ) i z
  let next := finRotate (n+1)
  let p' := fun b => p (v b)
  simp only [compressedArc,Fin.snoc_eq_cons_rotate,Finset.mul_sum,Matrix.sum_apply,compressed_ordered_color_sum,Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro d _
  let u' := fun b => u (d b) (v b) (v (next b))
  have h := compressed_cyclic_vertex_trace m L T ξ u' p' next
  simp only [mul_smul_comm] at h
  simp only [compressed_block_mark,normal_ordered_word_smul,Matrix.trace_smul,smul_eq_mul]
  change _ * (normalOrderedWord (fun b => compressedOpenFactor m L T ξ (u' b) (p' b) (p' (next b)))).trace = _
  rw [show (normalOrderedWord (fun b => compressedOpenFactor m L T ξ (u' b) (p' b) (p' (next b)))).trace =
    compressedLoopTrace m L T ξ u' p' from h]
  rfl

theorem compressed_labeled_source_coefficient {m : ℝ} (hm : 0 < m) (L : ℝ)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (p : κ → OSFourSpace)
    (u : H → κ → κ → UnitVector OSFourSpace) (W : H → κ → κ → ℂ) (n : ℕ) :
    iteratedDeriv (n+1) (compressedRelativeLog (compressedBlockSymbol m ξ p)
      (∑ c, compressedBlockVertex L T ξ p (u c) (W c))) 0 / (n+1).factorial =
      (-1:ℝ)^(n+1)*(∑ v : Fin (n+1) → κ, ∑ d : Fin (n+1) → H, compressedLabelCycle m L T ξ p u W v d).re/(n+1) := by
  rw [compressed_block_logdet_paths hm]
  simp_rw [compressed_labeled_cycle]
  let e := Fin.consEquiv (fun _ : Fin (n+1) => κ)
  rw [←e.sum_comp (fun v => ∑ d, compressedLabelCycle m L T ξ p u W v d),Fintype.sum_prod_type]
  rfl

end UV
