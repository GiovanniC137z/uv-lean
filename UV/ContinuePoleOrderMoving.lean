import UV.ContinuePoleOrderEuler

/-! Higher pole powers on common-height smooth tests. Repeated Euler
reduction transports the moving family into the existing fixed compact
C² test space for the simple pole. -/

noncomputable section

namespace UV.SectorPlane

open Filter MeasureTheory Set UV.Carrier
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

private theorem pole_order_euler_step_vanishes {K : TopologicalSpace.Compacts MassiveMomentum}
    (k : ℕ) {f : MassiveMomentum → ℂ} (hF : ∀ q, q ∉ K → f q = 0) :
    ∀ q, q ∉ K → poleOrderEulerStep k f q = 0 := by
  have hs : tsupport f ⊆ (K : Set MassiveMomentum) :=
    closure_minimal (fun q hq => by by_contra h; exact hq (hF q h)) K.isCompact.isClosed
  intro q hq
  have he : fderiv ℝ f q = 0 := fderiv_of_notMem_tsupport ℝ (fun h => hq (hs h))
  simp [poleOrderEulerStep, hF q hq, momentumEuler, he]

theorem pole_order_euler_test_vanishes {K : TopologicalSpace.Compacts MassiveMomentum}
    (n : ℕ) {f : MassiveMomentum → ℂ} (hF : ∀ q, q ∉ K → f q = 0) :
    ∀ q, q ∉ K → poleOrderEulerTest n f q = 0 := by
  induction n generalizing f with
  | zero => exact hF
  | succ n ih => exact ih (pole_order_euler_step_vanishes n hF)

private theorem pole_order_euler_family_step_contDiff (k : ℕ) {r : WithTop ℕ∞}
    {F : ℝ → MassiveMomentum → ℂ} (hF : ContDiff ℝ (r+1) (Function.uncurry F)) :
    ContDiff ℝ r (Function.uncurry (fun t => poleOrderEulerStep k (F t))) := by
  have H : ContDiff ℝ (r+1) (Function.uncurry
      (fun (z : ℝ × MassiveMomentum) (q : MassiveMomentum) => F z.1 q)) :=
    hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hd : ContDiff ℝ r (fun z : ℝ × MassiveMomentum => fderiv ℝ (F z.1) z.2) :=
    H.fderiv contDiff_snd le_rfl
  have hE : ContDiff ℝ r (fun z : ℝ × MassiveMomentum => momentumEuler (F z.1) z.2) :=
    hd.clm_apply contDiff_snd
  exact ((contDiff_const.mul (hF.of_le (by exact le_self_add))).add hE).div_const _

theorem pole_order_euler_family_contDiff (n : ℕ) (r : WithTop ℕ∞)
    {F : ℝ → MassiveMomentum → ℂ}
    (hF : ContDiff ℝ ((n : WithTop ℕ∞)+r) (Function.uncurry F)) :
    ContDiff ℝ r (Function.uncurry (fun t => poleOrderEulerTest n (F t))) := by
  induction n generalizing F with
  | zero => simpa only [poleOrderEulerTest, Nat.cast_zero, zero_add] using hF
  | succ n ih =>
    apply ih
    apply pole_order_euler_family_step_contDiff
    simpa only [Nat.cast_succ, add_right_comm] using hF

/-- A jointly C^(n+2) compact family converges against the literal moving
same-height pole of order n+1. The limiting Euler test uses height zero
and the original sector–evolution side. -/
theorem Plane.massive_same_side_pole_order_moving_boundary (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) (n : ℕ) (K : TopologicalSpace.Compacts MassiveMomentum)
    {F : ℝ → MassiveMomentum → ℂ}
    (hF : ContDiff ℝ ((n : WithTop ℕ∞)+2) (Function.uncurry F))
    (hFs : ∀ t q, q ∉ K → F t q = 0) :
    Tendsto (fun h : Height => ∫ q, F h q * (diamond.poleCoefficient ε h (massiveD m q))^(n+1))
      poleBoundaryHeights (𝓝 (bareComplexShellBoundary (diamond.eta ε) m (poleOrderEulerTest n (F 0)) /
        ((m ^ 2 : ℝ) : ℂ) ^ n)) := by
  let P (h : Height) (q : MassiveMomentum) := diamond.poleCoefficient ε h (massiveD m q)
  have hP (h : Height) : Continuous (P h) :=
    (diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)
  have hi (h : Height) : IntegrableOn (P h) (K : Set MassiveMomentum) :=
    (hP h).continuousOn.integrableOn_compact K.isCompact
  obtain ⟨T, hT⟩ := compact_momentum_boundary_functional K P hi
    (fun f => ⟨_, diamond.bare_massive_complex_c1 ε hm (f.contDiff.of_le (by norm_num)) f.compact_support⟩)
  choose L hL using fun h => compact_momentum_integral_exists K (P h) (hi h)
  let G (t : ℝ) := poleOrderEulerTest n (F t)
  have hG : ContDiff ℝ 2 (Function.uncurry G) := pole_order_euler_family_contDiff n 2 hF
  have hGs t : ∀ q, q ∉ K → G t q = 0 := pole_order_euler_test_vanishes n (hFs t)
  let j (t : ℝ) := CompactMomentumTest.ofFunction K (G t)
    (hG.comp (contDiff_const.prodMk contDiff_id)) (hGs t)
  have hj : Tendsto j (𝓝 0) (𝓝 (j 0)) := compact_momentum_slices_tendsto K G hG hGs 0
  have hmove := compact_momentum_moving_test_limit K L T
    (fun f => (hT f).congr fun h => (hL h f).symm) (hj.comp pole_height_tendsto_zero)
  letI : poleBoundaryHeights.NeBot := pole_boundary_heights_neBot
  have hT0 : T (j 0) = bareComplexShellBoundary (diamond.eta ε) m (G 0) := by
    apply tendsto_nhds_unique (hT (j 0))
    have H := diamond.bare_massive_complex_c1 ε hm ((j 0).contDiff.of_le (by norm_num)) (j 0).compact_support
    simpa only [j, CompactMomentumTest.ofFunction_value] using H
  rw [hT0] at hmove
  have hM := (diamond.square_mass_shift_tendsto ε m).pow n
  have hne : ((m ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sq_pos_of_pos hm).ne'
  refine (hmove.div hM (pow_ne_zero _ hne)).congr fun h => ?_
  apply (div_eq_iff (pow_ne_zero _ (diamond.square_mass_shift_ne_zero ε hm h))).mpr
  simp only [Function.comp_apply, hL, j, CompactMomentumTest.ofFunction_value]
  have hf : ContDiff ℝ (n : WithTop ℕ∞) (F h) :=
    (hF.comp (contDiff_const.prodMk contDiff_id)).of_le (by exact le_self_add)
  have hs : HasCompactSupport (F h) := HasCompactSupport.intro K.isCompact (hFs h)
  rw [← diamond.massive_pole_order_euler_reduction ε h m n hf hs, mul_comm]

theorem directed_pole_order_pow (z : ℂ) (n : ℕ) : directed (z ^ n) = (directed z)^n := by
  induction n with
  | zero => simpa only [pow_zero] using directed_one
  | succ n ih => rw [pow_succ, directed_mul, ih, pow_succ]

/-- The fixed-side result in the literal quotient, with every power of
the actual directed inverse at the same height. -/
theorem Plane.massive_same_side_pole_order_directed_boundary (diamond : Plane E) (ε : Evolution)
    {m : ℝ} (hm : 0 < m) (n : ℕ) {f : MassiveMomentum → ℂ}
    (hf : ContDiff ℝ ((n : WithTop ℕ∞)+1) f) (hs : HasCompactSupport f) :
    Tendsto (fun h : Height => ∫ q, directed (f q) * (diamond.poleInverse ε h (massiveD m q))^(n+1))
      poleBoundaryHeights (𝓝 (directed (bareComplexShellBoundary (diamond.eta ε) m (poleOrderEulerTest n f) /
        ((m ^ 2 : ℝ) : ℂ) ^ n))) := by
  have H := directed_shell_readout_continuous.continuousAt.tendsto.comp
    (diamond.massive_same_side_pole_order_boundary ε hm n hf hs)
  refine H.congr fun h => ?_
  have hP := (diamond.pole_coefficient_continuous ε h).comp (massiveD_continuous m)
  have hi : Integrable (fun q => f q * (diamond.poleCoefficient ε h (massiveD m q))^(n+1)) :=
    (hf.continuous.mul (hP.pow (n+1))).integrable_of_hasCompactSupport (μ := volume) hs.mul_right
  change directed (∫ q, f q * (diamond.poleCoefficient ε h (massiveD m q))^(n+1)) = _
  rw [← directed_integral hi]
  apply integral_congr_ae
  refine Eventually.of_forall fun q => ?_
  dsimp only
  rw [directed_mul, directed_pole_order_pow, diamond.pole_coefficient_eq_inv, diamond.pole_inverse_complex]
  rfl

end UV.SectorPlane
