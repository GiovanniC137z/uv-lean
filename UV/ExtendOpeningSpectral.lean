import UV.ExtendOpeningSelfAdjoint
import UV.ExtendOpeningBorelExp

/-! Every supplied spectral resolution of the actual self-adjoint
oscillator closure gives the already checked coherent vacuum vector.
The comparison is made on compact spectral cuts before exhausting
the real line. -/

noncomputable section

namespace UV

open Filter MeasureTheory Set
open scoped Topology Nat ComplexInnerProductSpace ENNReal

abbrev OpeningPositionClosure (ω : ℝ) := (openingPositionOnCore ω).closure

private def opening.spectralCut (n : ℕ) : Set ℝ := Icc (-(n : ℝ)) n

private theorem opening.spectralCut_measurable (n : ℕ) :
    MeasurableSet (opening.spectralCut n) := measurableSet_Icc

private def opening.cutCoordinate (n : ℕ) : ℝ → ℝ := (opening.spectralCut n).indicator id

private theorem opening.cutCoordinate_borel (n : ℕ) :
    sourceBoundedBorel (opening.cutCoordinate n) := by
  refine ⟨measurable_id.indicator (opening.spectralCut_measurable n), n, Nat.cast_nonneg n, ?_⟩
  intro x
  by_cases h : x ∈ opening.spectralCut n
  · simpa only [opening.cutCoordinate, indicator_of_mem h, id_eq] using (abs_le.mpr h)
  · simp [opening.cutCoordinate, indicator_of_notMem h]

private def opening.cutProjection {ω : ℝ} (R : SourceSpectralResolution (OpeningPositionClosure ω))
    (n : ℕ) : OpeningFock →L[ℂ] OpeningFock :=
  R.measure.projection (opening.spectralCut n)

private def opening.cutPosition {ω : ℝ} (R : SourceSpectralResolution (OpeningPositionClosure ω))
    (n : ℕ) : OpeningFock →L[ℂ] OpeningFock := R.calculus.operator (opening.cutCoordinate n)

private theorem opening.cutProjection_tendsto {ω : ℝ}
    (R : SourceSpectralResolution (OpeningPositionClosure ω)) (v : OpeningFock) :
    Tendsto (fun n => opening.cutProjection R n v) atTop (𝓝 v) := by
  have hm : Monotone opening.spectralCut := by
    intro n m hnm x hx
    have h : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact ⟨(neg_le_neg h).trans hx.1, hx.2.trans h⟩
  have hu : ⋃ n, opening.spectralCut n = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact ⟨n, abs_le.1 hn.le⟩
  simpa only [opening.cutProjection, hu, R.measure.univ, ContinuousLinearMap.one_apply] using
    sourcePVM_tendsto_iUnion R.measure opening.spectralCut opening.spectralCut_measurable hm v

private theorem opening.cut_acts_graph {ω : ℝ}
    (R : SourceSpectralResolution (OpeningPositionClosure ω)) (n : ℕ)
    (x : (OpeningPositionClosure ω).domain) :
    opening.cutPosition R n x = opening.cutProjection R n (OpeningPositionClosure ω x) := by
  let P := opening.cutProjection R n
  let f : ℝ → ℝ := (opening.spectralCut n).indicator (fun _ => 1)
  have hf : sourceBoundedBorel f := sourceBoundedBorel_indicator (opening.spectralCut_measurable n)
  have hfu : (fun u => u * f u) = opening.cutCoordinate n := by
    funext u
    by_cases h : u ∈ opening.spectralCut n <;> simp [f, opening.cutCoordinate, h]
  have hg := sourceResolution_borel_graph R f hf
    (hfu.symm ▸ opening.cutCoordinate_borel n) (x : OpeningFock)
  rw [hfu, R.calculus.indicator _ (opening.spectralCut_measurable n)] at hg
  have hc := sourceResolution_graph_commutes_bounded R P (fun s hs => by
    change R.measure.projection s * P = P * R.measure.projection s
    dsimp only [P, opening.cutProjection]
    rw [← R.measure.inter _ _ hs (opening.spectralCut_measurable n),
      ← R.measure.inter _ _ (opening.spectralCut_measurable n) hs, inter_comm])
  obtain ⟨u, hu⟩ := (OpeningPositionClosure ω).mem_graph_iff'.mp hg
  obtain ⟨v, hv⟩ := (OpeningPositionClosure ω).mem_graph_iff'.mp (hc x)
  have huv : u = v := Subtype.ext ((congrArg Prod.fst hu).trans (congrArg Prod.fst hv).symm)
  exact (congrArg Prod.snd hu).symm.trans (huv ▸ congrArg Prod.snd hv)

private theorem opening.cut_acts_projection {ω : ℝ}
    (R : SourceSpectralResolution (OpeningPositionClosure ω)) (n : ℕ) :
    opening.cutPosition R n * opening.cutProjection R n = opening.cutPosition R n := by
  rw [opening.cutPosition, opening.cutProjection, ← R.calculus.indicator _ (opening.spectralCut_measurable n),
    ← R.calculus.mul _ _ (opening.cutCoordinate_borel n)
      (sourceBoundedBorel_indicator (opening.spectralCut_measurable n))]
  congr 1
  funext t
  by_cases h : t ∈ opening.spectralCut n <;> simp [opening.cutCoordinate, h]

private theorem opening.cut_position_power {ω : ℝ}
    (R : SourceSpectralResolution (OpeningPositionClosure ω)) (n k : ℕ) :
    (opening.cutPosition R n ^ k) (opening.cutProjection R n (openingNumberState 0)) =
      opening.cutProjection R n (openingPositionVacuumPower ω k) := by
  induction k with
  | zero => simp [openingPositionVacuumPower_zero]
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih,
      ← ContinuousLinearMap.mul_apply, opening.cut_acts_projection]
    let T := openingPositionOnCore ω
    let x : T.closure.domain := ⟨openingPositionVacuumPower ω k, T.le_closure.1
      (openingPositionVacuumPower ω k).property⟩
    have he : T.closure x = (openingPositionVacuumPower ω (k + 1) : OpeningFock) := by
      rw [← openingPositionVacuumPower_succ]
      exact (T.le_closure.2 rfl).symm
    exact (opening.cut_acts_graph R n x).trans (congrArg (opening.cutProjection R n) he)

private theorem opening.cut_exp_vacuum {ω : ℝ}
    (R : SourceSpectralResolution (OpeningPositionClosure ω)) (n : ℕ) (ξ : ℝ) :
    (NormedSpace.exp ℂ (((ξ : ℂ) * Complex.I) • opening.cutPosition R n))
      (opening.cutProjection R n (openingNumberState 0)) =
      opening.cutProjection R n
        (openingCoherentVector (((ξ / Real.sqrt (2 * ω) : ℝ) : ℂ) * Complex.I)) := by
  let a := (ξ : ℂ) * Complex.I
  let P := opening.cutProjection R n
  let B := opening.cutPosition R n
  let ev : (OpeningFock →L[ℂ] OpeningFock) →L[ℂ] OpeningFock :=
    ContinuousLinearMap.apply ℂ OpeningFock (P (openingNumberState 0))
  have ha := ev.hasSum (NormedSpace.expSeries_summable' (𝕂 := ℂ) (a • B)).hasSum
  have hb := P.hasSum (openingPositionVacuumExponential_hasSum ω ξ)
  change ev (NormedSpace.exp ℂ (a • B)) = _
  rw [NormedSpace.exp_eq_tsum]
  refine ha.tsum_eq.symm.trans ((tsum_congr fun k => ?_).trans hb.tsum_eq)
  have hcomm : Commute (algebraMap ℂ (OpeningFock →L[ℂ] OpeningFock) a) B :=
    Algebra.commutes _ _
  have hp : (a • B) ^ k = a ^ k • B ^ k := by
    rw [Algebra.smul_def a, hcomm.mul_pow, ← map_pow, ← Algebra.smul_def]
  rw [hp, smul_smul, ← div_eq_inv_mul, map_smul, map_smul]
  exact congrArg ((a ^ k / (k ! : ℂ)) • ·) (opening.cut_position_power R n k)

private theorem opening.borel_equal_on_cut {ω : ℝ}
    (R : SourceSpectralResolution (OpeningPositionClosure ω)) (n : ℕ)
    {f g : ℝ → ℝ} (hf : sourceBoundedBorel f) (hg : sourceBoundedBorel g)
    (heq : EqOn f g (opening.spectralCut n)) :
    R.calculus.operator f * opening.cutProjection R n =
      opening.cutProjection R n * R.calculus.operator g := by
  rw [opening.cutProjection, ← R.calculus.indicator _ (opening.spectralCut_measurable n),
    ← R.calculus.mul _ _ hf (sourceBoundedBorel_indicator (opening.spectralCut_measurable n)),
    ← R.calculus.mul _ _ (sourceBoundedBorel_indicator (opening.spectralCut_measurable n)) hg]
  congr 1
  funext t
  by_cases ht : t ∈ opening.spectralCut n
  · simp [ht, heq ht]
  · simp [ht]

private theorem opening.purePhase_bounded {f : ℝ → ℝ} (hf : Measurable f) (ξ : ℝ) :
    let U (t : ℝ) := Complex.exp (((ξ : ℂ) * Complex.I) * (f t : ℂ))
    sourceBoundedBorel (fun t => (U t).re) ∧ sourceBoundedBorel (fun t => (U t).im) := by
  let U (t : ℝ) := Complex.exp (((ξ : ℂ) * Complex.I) * (f t : ℂ))
  have hm : Measurable U := by
    dsimp [U]
    fun_prop
  have hn (t : ℝ) : ‖U t‖ = 1 := by
    simp [U, Complex.norm_exp, Complex.mul_re]
  exact ⟨⟨Complex.continuous_re.measurable.comp hm, 1, zero_le_one,
    fun t => hn t ▸ Complex.abs_re_le_norm (U t)⟩,
    ⟨Complex.continuous_im.measurable.comp hm, 1, zero_le_one,
    fun t => hn t ▸ Complex.abs_im_le_norm (U t)⟩⟩

/-- The bounded complex phase from a spectral resolution of the closure. -/
def openingPositionSpectralExponential {ω : ℝ}
    (R : SourceSpectralResolution (OpeningPositionClosure ω)) (ξ : ℝ) :
    OpeningFock →L[ℂ] OpeningFock :=
  openingComplexBorel R.calculus (fun t => Complex.exp (((ξ : ℂ) * Complex.I) * (t : ℂ)))

/-- The spectral exponential on the actual unbounded oscillator closure
agrees on the vacuum with the previously constructed coherent vector for
every compatible spectral resolution. -/
theorem openingPositionSpectralExponential_vacuum {ω : ℝ}
    (R : SourceSpectralResolution (OpeningPositionClosure ω)) (ξ : ℝ) :
    openingPositionSpectralExponential R ξ (openingNumberState 0) =
      openingCoherentVector (((ξ / Real.sqrt (2 * ω) : ℝ) : ℂ) * Complex.I) := by
  let a := (ξ : ℂ) * Complex.I
  let vac := openingNumberState 0
  let F := openingPositionSpectralExponential R ξ
  let co := openingCoherentVector (((ξ / Real.sqrt (2 * ω) : ℝ) : ℂ) * Complex.I)
  have hcut (n : ℕ) : opening.cutProjection R n (F vac) = opening.cutProjection R n co := by
    let f := opening.cutCoordinate n
    let g (t : ℝ) := Complex.exp (a * (f t : ℂ))
    let h (t : ℝ) := Complex.exp (a * (t : ℂ))
    have hb := opening.purePhase_bounded (opening.cutCoordinate_borel n).1 ξ
    have hb' := opening.purePhase_bounded measurable_id ξ
    have he : EqOn g h (opening.spectralCut n) := by
      intro t ht
      dsimp [g, h]
      rw [show f t = t by simp [f, opening.cutCoordinate, ht]]
    have hr := opening.borel_equal_on_cut R n hb.1 hb'.1
      (fun t ht => congrArg Complex.re (he ht))
    have hi := opening.borel_equal_on_cut R n hb.2 hb'.2
      (fun t ht => congrArg Complex.im (he ht))
    have hmul : openingComplexBorel R.calculus g * opening.cutProjection R n =
        opening.cutProjection R n * F := by
      change openingComplexBorel R.calculus g * _ = _ * openingComplexBorel R.calculus h
      rw [openingComplexBorel, openingComplexBorel, add_mul, mul_add, smul_mul_assoc,
        mul_smul_comm, hr, hi]
      rfl
    have hgm := openingBorel_exponential R.calculus f (opening.cutCoordinate_borel n) a
    change openingComplexBorel R.calculus g = NormedSpace.exp ℂ (a • opening.cutPosition R n) at hgm
    rw [hgm] at hmul
    exact (congrArg (fun A : OpeningFock →L[ℂ] OpeningFock => A vac) hmul).symm.trans
      (opening.cut_exp_vacuum R n ξ)
  exact tendsto_nhds_unique (opening.cutProjection_tendsto R (F vac))
    ((opening.cutProjection_tendsto R co).congr fun n => (hcut n).symm)

/-- For the stated phase on the selected invariant, the supplied spectral
exponential has the exact Poisson channel weights. -/
theorem openingPositionSpectralExponential_on_cut_poisson {ω ξ b S : ℝ}
    (R : SourceSpectralResolution (OpeningPositionClosure ω))
    (hω : 0 < ω) (hphase : ξ ^ 2 / (2 * ω) = b * S) (n : ℕ) :
    ‖inner ℂ (openingNumberState n)
      (openingPositionSpectralExponential R ξ (openingNumberState 0))‖ ^ 2 =
        ProbabilityTheory.poissonPMFReal (b * S).toNNReal n := by
  rw [openingPositionSpectralExponential_vacuum R ξ, openingNumberState_on_cut_poisson hω hphase]

end UV
