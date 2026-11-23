import UV.ContinueMomentumRoutingFourier
import UV.ContinueNormalZeroIdentification

/-! Physical signs, normalizations and winding masks for a mixed
connected graph of the affine comparison. Every cutoff and every graph
is taken at fixed finite electromagnetic order. -/

noncomputable section

open Classical Finset Filter MeasureTheory MeasureTheory.Measure UV.SectorPlane
open scoped Matrix.Norms.L2Operator Topology

namespace UV

variable {V : Type*} [Fintype V] {m L : ℝ}

theorem momentum_open_frequency_terminal {r : ℕ} (m ξ : ℝ) (u : Fin r → UnitVector OSFourSpace) (p : Fin (r+1) → OSFourSpace) :
    normalOrderedWord (fun i => normalDiracFrequency m (p i) ξ * normalOpenVertex u i) =
      normalOrderedWord (fun i : Fin r => normalDiracFrequency m (p i.castSucc) ξ * diracSlash (u i).val) *
        normalDiracFrequency m (p (Fin.last r)) ξ := by
  unfold normalOrderedWord
  rw [List.ofFn_succ']
  simp only [normalOpenVertex,Fin.lastCases_castSucc,Fin.lastCases_last,List.concat_eq_append,List.prod_append,List.prod_cons,List.prod_nil,mul_one]

theorem momentum_periodic_closed_selected {n : ℕ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ) (w : ℤ)
    (hw : w ≠ 0 ∨ 5 < n+1) (u : Fin (n+1) → UnitVector OSFourSpace) (p : Fin (n+1) → OSFourSpace) :
    L^n • (∫ t in normalUnitCell n, ∑' h : Fin n → ℤ, normalWindingTrace m L (-θ) w u p (fun j => L*(t j+(h j:ℝ)))) =
      if w = 0 then ∫ ξ,normalZeroTrace m L u p ξ else ∫ x,normalWindingTrace m L (-θ) w u p x := by
  rw [normal_periodic_winding_integral hm hL]
  by_cases h : w = 0
  · subst w
    rw [if_pos rfl]
    cases n with
    | zero => simp at hw
    | succ n => exact normal_winding_zero_frequency_identity hm (-θ) u p
  · rw [if_neg h]

/-- Closed sectors already include their center and winding phase.
For an open path its only normal phase is the twisted endpoint phase. -/
def MomentumProtectedComponent.phase (w : ℤ) : MomentumProtectedComponent L → ℂ
  | .loop .. => 1
  | .line θ _ _ _ _ z z' => normalAngularPhase θ ((z'.val-z.val)/L+(w:ℝ))

theorem MomentumProtectedComponent.phase_norm (w : ℤ) (P : MomentumProtectedComponent L) : ‖P.phase w‖ = 1 := by
  cases P <;> first | exact norm_one | exact normal_angular_phase_norm _ _

def momentumPhysicalPhase (S : V → MomentumProtectedComponent L) (w : V → ℤ) : ℂ := ∏ v,(S v).phase (w v)

theorem momentum_physical_phase_norm (S : V → MomentumProtectedComponent L) (w : V → ℤ) : ‖momentumPhysicalPhase S w‖ = 1 := by
  simp [momentumPhysicalPhase,norm_prod,MomentumProtectedComponent.phase_norm]

/-- The tree and even the representation space may depend on the finite
mask. The signed value is bounded after selecting the actual branch
for each individual winding. The constant c may include the cyclic
source symmetry factor and the product of the unit i marks. -/
theorem momentum_selected_physical_graph (S : V → MomentumProtectedComponent L)
    {Z : (V → Bool) → Type*} [∀ b,MeasurableSpace (Z b)] (σ : Measure OSFourSpace) (μ : ∀ b,Measure (Z b))
    (s : (b : V → Bool) → (V → ℤ) → (v : V) → Z b → Fin (((S v).sector (b v)).segments) → OSFourSpace)
    (Δ : (b : V → Bool) → V → Z b → OSFourSpace) (W : (b : V → Bool) → Z b → ℂ)
    (h : ∀ b,NormalGraphAbsolute σ (μ b) m (fun v => (S v).sector (b v)) (s b) (Δ b) (W b)) (c : ℂ) :
    let pick := fun (w : V → ℤ) v => decide (w v = 0)
    let F := fun w => normalGraphTerm m (fun v => (S v).sector (pick w v)) (s (pick w)) (Δ (pick w)) (W (pick w)) w
    let ν := fun w => normalGraphMeasure σ (fun v => (S v).sector (pick w v)) (μ (pick w))
    let H := fun w t => (c*momentumPhysicalPhase S w)*F w t
    (∀ w,Integrable (H w) (ν w)) ∧ Summable (fun w => ∫ t,‖H w t‖ ∂ν w) := by
  intro pick F ν H
  let F₀ := fun b => normalGraphTerm m (fun v => (S v).sector (b v)) (s b) (Δ b) (W b)
  let ν₀ := fun b => normalGraphMeasure σ (fun v => (S v).sector (b v)) (μ b)
  have hs := normal_finite_winding_partition (fun b w => ∫ t,‖F₀ b w t‖ ∂ν₀ b) (fun _ _ => integral_nonneg fun _ => norm_nonneg _)
    (fun b => (h b).2) pick
  refine ⟨fun w => ((h (pick w)).1 w).const_mul _,?_⟩
  convert hs.mul_left ‖c‖ using 1
  funext w
  simp only [H,norm_mul,momentum_physical_phase_norm,mul_one,integral_const_mul]
  rfl

/-- Unrestricted graph integrals are limits of simultaneous ultraviolet
cutoffs which tend to one pointwise, including smooth or sharp cutoffs.
The domination is uniform enough to remove cutoffs through the winding sum. -/
theorem momentum_winding_remove_cutoffs {I : Type*} {X : I → Type*} [∀ i, MeasurableSpace (X i)] (ν : (i : I) → Measure (X i))
    (F : (i : I) → X i → ℂ) (hi : ∀ i,Integrable (F i) (ν i)) (hs : Summable (fun i => ∫ t, ‖F i t‖ ∂ν i))
    (χ : ℕ → (i : I) → X i → ℂ) (hχ : ∀ n i,Measurable (χ n i)) (hb : ∀ n i t, ‖χ n i t‖ ≤ 1)
    (ht : ∀ i, ∀ᵐ t ∂ν i, Tendsto (fun n => χ n i t) atTop (𝓝 1)) :
    Tendsto (fun n => ∑' i, ∫ t,χ n i t * F i t ∂ν i) atTop (𝓝 (∑' i, ∫ t,F i t ∂ν i)) := by
  have hle (n i t) : ‖χ n i t*F i t‖ ≤ ‖F i t‖ := (norm_mul ..).le.trans (mul_le_of_le_one_left (norm_nonneg _) (hb n i t))
  have hm (n i) := (hχ n i).aestronglyMeasurable.mul (hi i).aestronglyMeasurable
  apply tendsto_tsum_of_dominated_convergence hs
  · intro i
    apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖F i t‖) (Eventually.of_forall fun n => hm n i)
      (Eventually.of_forall fun n => Eventually.of_forall fun t => hle n i t) (hi i).norm
    exact (ht i).mono fun t h => by simpa only [one_mul] using h.mul_const (F i t)
  · apply Eventually.of_forall fun n i => ?_
    apply (norm_integral_le_integral_norm _).trans
    exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hi i).norm (Eventually.of_forall fun t => hle n i t)

end UV
