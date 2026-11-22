import UV.ExtendOpeningAdjoint
import Mathlib.Analysis.PSeries

/-! The closure of the oscillator position is self-adjoint. Approximate
the graph of its adjoint by the same number truncation in both coordinates.
The only error consists of the two adjacent number slots at the cutoff.
Square summability and divergence of the harmonic series make this error
arbitrarily small along an escaping sequence of cutoffs. -/

noncomputable section

namespace UV

open Filter
open scoped Nat Topology ComplexInnerProductSpace ENNReal

private def opening.trunc (n : ℕ) (v : OpeningFock) : OpeningFock :=
  ∑ i ∈ Finset.range (n + 1), lp.single 2 i (v i)

@[simp] private theorem opening.trunc_apply (n : ℕ) (v : OpeningFock) (k : ℕ) :
    opening.trunc n v k = if k ≤ n then v k else 0 := by
  simp [opening.trunc, Finset.sum_apply, lp.coeFn_single, Pi.single_apply, Nat.lt_succ_iff]

private theorem opening.trunc_tendsto (v : OpeningFock) :
    Tendsto (fun n : ℕ => opening.trunc n v) atTop (𝓝 v) :=
  (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) v).tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)

private def opening.truncDomain (ω : ℝ) (n : ℕ) (v : OpeningFock) :
    (openingPositionOnCore ω).domain :=
  ⟨opening.trunc n v, ⟨n, fun k hk => by simp [not_le.mpr hk]⟩⟩

private def opening.truncError (ω : ℝ) (v : OpeningFock) (n : ℕ) : OpeningFock :=
  -(openingPositionScale ω * (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) * v (n + 1)) •
    openingNumberState n +
    (openingPositionScale ω * (Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ) * v n) •
      openingNumberState (n + 1)

private theorem opening.trunc_error_formula (ω : ℝ)
    (v : (openingPositionOnCore ω).adjoint.domain) (n : ℕ) :
    openingPositionOnCore ω (opening.truncDomain ω n v) -
      opening.trunc n ((openingPositionOnCore ω).adjoint v) =
        opening.truncError ω v n := by
  ext k
  simp only [lp.coeFn_sub, Pi.sub_apply, openingPositionOnCore_apply, opening.trunc_apply,
    openingPositionOnCore_adjoint_coordinate, opening.truncError, lp.coeFn_add,
    lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, openingNumberState_coordinate]
  change openingPositionScale ω * openingJacobi (opening.trunc n v) k -
    (if k ≤ n then openingPositionScale ω * openingJacobi v k else 0) = _
  simp only [openingJacobi, opening.trunc_apply]
  rcases lt_trichotomy k n with h | h | h
  · simp [show k + 1 ≤ n by omega, show k - 1 ≤ n by omega, le_of_lt h,
      show n ≠ k by omega, show n + 1 ≠ k by omega]
  · subst k
    simp [show ¬ n + 1 ≤ n by omega, show n - 1 ≤ n by omega]
    ring
  · by_cases h' : k = n + 1
    · subst k
      simp [show ¬ n + 1 + 1 ≤ n by omega, show ¬ n + 1 ≤ n by omega]
      ring
    · simp [show ¬ k + 1 ≤ n by omega, show ¬ k - 1 ≤ n by omega, not_le.mpr h,
        show n ≠ k by omega, Ne.symm h']

private theorem opening.small_adjacent_pair (v : OpeningFock) (N : ℕ)
    {q : ℝ} (hq : 0 < q) : ∃ n ≥ N, (n + 1 : ℝ) * (‖v n‖ ^ 2 + ‖v (n + 1)‖ ^ 2) < q := by
  by_contra! h
  have hs : Summable (fun n : ℕ => ‖v n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using
      (lp.memℓp v).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hss := hs.add ((summable_nat_add_iff (f := fun n : ℕ => ‖v n‖ ^ 2) 1).2 hs)
  have hharm : Summable (fun n : ℕ => q / ((n + (N + 1) : ℕ) : ℝ)) := by
    apply ((summable_nat_add_iff N).2 hss).of_nonneg_of_le
    · intro n
      positivity
    · intro n
      push_cast
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + ((N : ℝ) + 1))).2
      simpa only [Nat.cast_add, add_assoc, mul_comm] using h (n + N) (by omega)
  have hharm' : Summable (fun n : ℕ => 1 / ((n + (N + 1) : ℕ) : ℝ)) := by
    convert hharm.mul_left q⁻¹ using 1
    funext n
    field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff (N + 1)).1 hharm')

private theorem opening.small_trunc_error (ω : ℝ) (v : OpeningFock) (N : ℕ)
    {ε : ℝ} (hε : 0 < ε) : ∃ n ≥ N, ‖opening.truncError ω v n‖ < ε := by
  let δ := ε / (2 * (‖openingPositionScale ω‖ + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨n, hn, h⟩ := opening.small_adjacent_pair v N (sq_pos_of_pos hδ)
  refine ⟨n, hn, ?_⟩
  let w := Real.sqrt ((n + 1 : ℕ) : ℝ)
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  have hw₂ : w ^ 2 = (n : ℝ) + 1 := by
    dsimp [w]
    rw [Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_add, Nat.cast_one]
  have h₁ : w * ‖v n‖ < δ := by
    refine (sq_lt_sq₀ (mul_nonneg hw (norm_nonneg _)) hδ.le).1 ?_
    rw [mul_pow, hw₂]
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) (sq_nonneg ‖v (n + 1)‖)]
  have h₂ : w * ‖v (n + 1)‖ < δ := by
    refine (sq_lt_sq₀ (mul_nonneg hw (norm_nonneg _)) hδ.le).1 ?_
    rw [mul_pow, hw₂]
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) (sq_nonneg ‖v n‖)]
  have hns (k : ℕ) : ‖openingNumberState k‖ = 1 := by
    simp [openingNumberState, lp.norm_single]
  calc
    _ ≤ ‖openingPositionScale ω‖ * (w * ‖v (n + 1)‖) +
        ‖openingPositionScale ω‖ * (w * ‖v n‖) := by
      unfold opening.truncError
      simpa only [norm_smul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hw, hns, mul_one, mul_assoc] using
        (norm_add_le (-(openingPositionScale ω * (w : ℂ) * v (n + 1)) • openingNumberState n)
          ((openingPositionScale ω * (w : ℂ) * v n) • openingNumberState (n + 1)))
    _ ≤ (‖openingPositionScale ω‖ + 1) * (w * ‖v (n + 1)‖) +
        (‖openingPositionScale ω‖ + 1) * (w * ‖v n‖) := by
      gcongr <;> linarith
    _ < (‖openingPositionScale ω‖ + 1) * δ + (‖openingPositionScale ω‖ + 1) * δ :=
      add_lt_add (mul_lt_mul_of_pos_left h₂ (by positivity)) (mul_lt_mul_of_pos_left h₁ (by positivity))
    _ = ε := by dsimp [δ]; field_simp; ring

private theorem opening.adjoint_graph_subset_closure (ω : ℝ) :
    (openingPositionOnCore ω).adjoint.graph ≤ (openingPositionOnCore ω).graph.topologicalClosure := by
  intro p h
  obtain ⟨v', hv⟩ := ((openingPositionOnCore ω).adjoint.mem_graph_iff').mp h
  rw [← hv]
  let v : OpeningFock := v'
  let w := (openingPositionOnCore ω).adjoint v'
  change (v, w) ∈ closure ((openingPositionOnCore ω).graph : Set (OpeningFock × OpeningFock))
  refine Metric.mem_closure_iff.mpr (fun ε hε => ?_)
  have hlim (x : OpeningFock) :
      ∀ᶠ n in atTop, dist x (opening.trunc n x) < ε / 2 := by
    simpa only [dist_comm] using (Metric.tendsto_nhds.mp (opening.trunc_tendsto x) _ (half_pos hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hlim v).and (hlim w))
  obtain ⟨n, hn, he⟩ := opening.small_trunc_error ω v N (half_pos hε)
  let x := opening.truncDomain ω n v
  refine ⟨(x, openingPositionOnCore ω x), (openingPositionOnCore ω).mem_graph x, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  refine ⟨(hN n hn).1.trans (half_lt_self hε), ?_⟩
  have hdiff : openingPositionOnCore ω x - opening.trunc n w = opening.truncError ω v n :=
    opening.trunc_error_formula ω v' n
  have hb : dist (opening.trunc n w) (openingPositionOnCore ω x) < ε / 2 := by
    rw [dist_comm, dist_eq_norm, hdiff]
    exact he
  linarith [dist_triangle w (opening.trunc n w) (openingPositionOnCore ω x), (hN n hn).2]

theorem openingPositionOnCore_closable (ω : ℝ) :
    (openingPositionOnCore ω).IsClosable := by
  have hle : openingPositionOnCore ω ≤ (openingPositionOnCore ω).adjoint :=
    LinearPMap.IsFormalAdjoint.le_adjoint (openingPositionOnCore_dense ω)
      (openingPositionOnCore_symmetric ω)
  exact ((LinearPMap.adjoint_isClosed (openingPositionOnCore_dense ω)).isClosable).leIsClosable hle

theorem openingPositionClosure_eq_adjoint (ω : ℝ) :
    (openingPositionOnCore ω).closure = (openingPositionOnCore ω).adjoint := by
  apply LinearPMap.eq_of_eq_graph
  rw [← (openingPositionOnCore_closable ω).graph_closure_eq_closure_graph]
  apply le_antisymm _ (opening.adjoint_graph_subset_closure ω)
  have hle : openingPositionOnCore ω ≤ (openingPositionOnCore ω).adjoint :=
    LinearPMap.IsFormalAdjoint.le_adjoint (openingPositionOnCore_dense ω)
      (openingPositionOnCore_symmetric ω)
  have h := Submodule.topologicalClosure_mono (LinearPMap.le_graph_of_le hle)
  exact h.trans_eq (LinearPMap.adjoint_isClosed (openingPositionOnCore_dense ω)).submodule_topologicalClosure_eq

private theorem opening.graph_adjoint_closure (g : Submodule ℂ (OpeningFock × OpeningFock)) :
    g.topologicalClosure.adjoint = g.adjoint := by
  ext x
  simp only [Submodule.mem_adjoint_iff]
  constructor
  · exact fun h a b hab => h a b (g.le_topologicalClosure hab)
  · intro h a b hab
    have hc : IsClosed {p : OpeningFock × OpeningFock |
        inner ℂ p.2 x.1 - inner ℂ p.1 x.2 = 0} :=
      isClosed_eq ((continuous_snd.inner continuous_const).sub
        (continuous_fst.inner continuous_const)) continuous_const
    exact closure_minimal (fun p hp => h p.1 p.2 hp) hc hab

/-- The closure of the actual frequency-scaled oscillator number rule is
a self-adjoint operator on the positive Hilbert space. -/
theorem openingPositionClosure_selfAdjoint (ω : ℝ) :
    IsSelfAdjoint (openingPositionOnCore ω).closure := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  have hd : Dense ((openingPositionOnCore ω).closure.domain : Set OpeningFock) :=
    (openingPositionOnCore_dense ω).mono (openingPositionOnCore ω).le_closure.1
  calc
    _ = (openingPositionOnCore ω).closure.graph.adjoint :=
      LinearPMap.adjoint_graph_eq_graph_adjoint hd
    _ = (openingPositionOnCore ω).graph.adjoint := by
      rw [← (openingPositionOnCore_closable ω).graph_closure_eq_closure_graph,
        opening.graph_adjoint_closure]
    _ = (openingPositionOnCore ω).adjoint.graph :=
      (LinearPMap.adjoint_graph_eq_graph_adjoint (openingPositionOnCore_dense ω)).symm
    _ = _ := by rw [openingPositionClosure_eq_adjoint ω]

end UV
