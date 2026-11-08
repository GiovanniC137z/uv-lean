import UV.CliffordContact
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Radial contact obstructions on the exterior of a ball. All Hessians below
are actual iterated derivatives of the radial scalar potential. -/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Matrix Topology Matrix.Norms.Elementwise RealInnerProductSpace

namespace UV

private theorem sum_fin4_real (f : Fin 4 → ℝ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 := by
  simp only [Fin.sum_univ_succ]
  change f 0 + (f 1 + (f 2 + (f 3 + 0))) = _
  ring

def radialDamperPotential (F : ℝ → ℝ) (u : ℝ) : ℝ := -Real.log (F u)

def radialFirstPartial (h : ℝ → ℝ) (k : DiracMomentum) (μ : Fin 4) : ℝ :=
  deriv (fun r : ℝ => h (‖k + r • EuclideanSpace.single μ 1‖ ^ 2)) 0

def radialScalarHessian (h : ℝ → ℝ) (k : DiracMomentum) (μ ν : Fin 4) : ℝ :=
  deriv (fun r : ℝ => radialFirstPartial h (k + r • EuclideanSpace.single ν 1) μ) 0

theorem radialPotential_direction_hasDeriv {h h₁ : ℝ → ℝ} {u₀ : ℝ}
    (hh : ∀ u, u₀ < u → HasDerivAt h (h₁ u) u)
    (k : DiracMomentum) (hk : u₀ < ‖k‖ ^ 2) (μ : Fin 4) :
    HasDerivAt (fun r : ℝ => h (‖k + r • EuclideanSpace.single μ 1‖ ^ 2))
      (2 * h₁ (‖k‖ ^ 2) * k μ) 0 := by
  have hd : HasDerivAt h (h₁ (‖k‖ ^ 2))
      (‖k + (0 : ℝ) • EuclideanSpace.single μ 1‖ ^ 2) := by
    simpa only [zero_smul, add_zero] using hh (‖k‖ ^ 2) hk
  convert hd.comp 0 (normSq_single_hasDeriv k μ) using 1
  ring

theorem radialFirstPartial_eq {h h₁ : ℝ → ℝ} {u₀ : ℝ}
    (hh : ∀ u, u₀ < u → HasDerivAt h (h₁ u) u)
    (k : DiracMomentum) (hk : u₀ < ‖k‖ ^ 2) (μ : Fin 4) :
    radialFirstPartial h k μ = 2 * h₁ (‖k‖ ^ 2) * k μ :=
  (radialPotential_direction_hasDeriv hh k hk μ).deriv

theorem radialGradient_direction_hasDeriv {h₁ h₂ : ℝ → ℝ} {u₀ : ℝ}
    (hh₁ : ∀ u, u₀ < u → HasDerivAt h₁ (h₂ u) u)
    (k : DiracMomentum) (hk : u₀ < ‖k‖ ^ 2) (μ ν : Fin 4) :
    HasDerivAt (fun r : ℝ => 2 * h₁ (‖k + r • EuclideanSpace.single ν 1‖ ^ 2) *
      (k + r • EuclideanSpace.single ν (1 : ℝ) : DiracMomentum) μ)
      (2 * h₁ (‖k‖ ^ 2) * (if μ = ν then 1 else 0) + 4 * h₂ (‖k‖ ^ 2) * k μ * k ν) 0 := by
  have hd : HasDerivAt h₁ (h₂ (‖k‖ ^ 2))
      (‖k + (0 : ℝ) • EuclideanSpace.single ν 1‖ ^ 2) := by
    simpa only [zero_smul, add_zero] using hh₁ (‖k‖ ^ 2) hk
  have hc : HasDerivAt
      (fun r : ℝ => (k + r • EuclideanSpace.single ν (1 : ℝ) : DiracMomentum) μ)
      (if μ = ν then (1 : ℝ) else 0) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const
      (if μ = ν then (1 : ℝ) else 0)).const_add (k μ) using 1
    · ext r
      simp [PiLp.add_apply, PiLp.smul_apply, EuclideanSpace.single_apply]
    · simp
  have hg := ((hd.comp 0 (normSq_single_hasDeriv k ν)).fun_mul hc).const_mul 2
  simp only [Function.comp_def, zero_smul, add_zero] at hg
  convert hg using 1
  · ext r
    ring
  · ring

theorem radialScalarHessian_eq {h h₁ h₂ : ℝ → ℝ} {u₀ : ℝ}
    (hh : ∀ u, u₀ < u → HasDerivAt h (h₁ u) u)
    (hh₁ : ∀ u, u₀ < u → HasDerivAt h₁ (h₂ u) u)
    (k : DiracMomentum) (hk : u₀ < ‖k‖ ^ 2) (μ ν : Fin 4) :
    radialScalarHessian h k μ ν =
      2 * h₁ (‖k‖ ^ 2) * (if μ = ν then 1 else 0) + 4 * h₂ (‖k‖ ^ 2) * k μ * k ν := by
  have hc : Tendsto (fun r : ℝ => ‖k + r • EuclideanSpace.single ν 1‖ ^ 2)
      (𝓝 0) (𝓝 (‖k‖ ^ 2)) := by
    simpa only [zero_smul, add_zero] using (normSq_single_hasDeriv k ν).continuousAt.tendsto
  have he : (fun r : ℝ => radialFirstPartial h (k + r • EuclideanSpace.single ν 1) μ) =ᶠ[𝓝 0]
      (fun r : ℝ => 2 * h₁ (‖k + r • EuclideanSpace.single ν 1‖ ^ 2) *
        (k + r • EuclideanSpace.single ν (1 : ℝ) : DiracMomentum) μ) := by
    filter_upwards [hc.eventually (Ioi_mem_nhds hk)] with r hr
    exact radialFirstPartial_eq hh _ hr μ
  exact he.deriv_eq.trans (radialGradient_direction_hasDeriv hh₁ k hk μ ν).deriv

def generalContactDifference (h : ℝ → ℝ) (e : ℝ) (k : DiracMomentum) (μ ν : Fin 4) : ℝ :=
  4 * e ^ 2 * radialScalarHessian h k μ ν

theorem generalContactDifference_explicit {h h₁ h₂ : ℝ → ℝ} {u₀ : ℝ}
    (hh : ∀ u, u₀ < u → HasDerivAt h (h₁ u) u)
    (hh₁ : ∀ u, u₀ < u → HasDerivAt h₁ (h₂ u) u)
    (e : ℝ) (k : DiracMomentum) (hk : u₀ < ‖k‖ ^ 2) (μ ν : Fin 4) :
    generalContactDifference h e k μ ν =
      8 * e ^ 2 * h₁ (‖k‖ ^ 2) * (if μ = ν then 1 else 0) +
        16 * e ^ 2 * h₂ (‖k‖ ^ 2) * k μ * k ν := by
  rw [generalContactDifference, radialScalarHessian_eq hh hh₁ k hk]
  ring

theorem generalContactDifference_trace {h h₁ h₂ : ℝ → ℝ} {u₀ : ℝ}
    (hh : ∀ u, u₀ < u → HasDerivAt h (h₁ u) u)
    (hh₁ : ∀ u, u₀ < u → HasDerivAt h₁ (h₂ u) u)
    (e : ℝ) (k : DiracMomentum) (hk : u₀ < ‖k‖ ^ 2) :
    (∑ μ, generalContactDifference h e k μ μ) =
      32 * e ^ 2 * h₁ (‖k‖ ^ 2) + 16 * e ^ 2 * ‖k‖ ^ 2 * h₂ (‖k‖ ^ 2) := by
  simp_rw [generalContactDifference_explicit hh hh₁ e k hk]
  rw [sum_fin4_real]
  simp only [ite_true, mul_one]
  rw [diracMomentum_norm_sq]
  ring

def generalContactRadialTrace (e : ℝ) (h₁ h₂ : ℝ → ℝ) (r : ℝ) : ℝ :=
  32 * e ^ 2 * h₁ (r ^ 2) + 16 * e ^ 2 * r ^ 2 * h₂ (r ^ 2)

def generalContactFluxPrimitive (e : ℝ) (h₁ : ℝ → ℝ) (r : ℝ) : ℝ :=
  8 * e ^ 2 * r ^ 4 * h₁ (r ^ 2)

theorem generalContactFluxPrimitive_hasDeriv {h₁ h₂ : ℝ → ℝ} {u₀ : ℝ}
    (hh₁ : ∀ u, u₀ < u → HasDerivAt h₁ (h₂ u) u)
    (e r : ℝ) (hr : u₀ < r ^ 2) :
    HasDerivAt (generalContactFluxPrimitive e h₁)
      (r ^ 3 * generalContactRadialTrace e h₁ h₂ r) r := by
  have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    simpa only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, mul_one, pow_one] using
      (hasDerivAt_id r).pow 2
  have hc := (hh₁ (r ^ 2) hr).comp r (h := fun x : ℝ => x ^ 2) hp
  have h := (((hasDerivAt_id r).pow 4).fun_mul hc).const_mul (8 * e ^ 2)
  simp only [Function.comp_def, id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, mul_one] at h
  convert h using 1
  · ext x
    unfold generalContactFluxPrimitive
    ring
  · unfold generalContactRadialTrace
    ring

theorem generalContact_flux_interval {h₁ h₂ : ℝ → ℝ} {u₀ R₀ R : ℝ}
    (hh₁ : ∀ u, u₀ < u → HasDerivAt h₁ (h₂ u) u)
    (hh₂ : ContinuousOn h₂ (Ioi u₀)) (hR₀ : 0 < R₀) (hbase : u₀ < R₀ ^ 2)
    (hR : R₀ ≤ R) (e : ℝ) :
    (∫ r in R₀..R, r ^ 3 * generalContactRadialTrace e h₁ h₂ r) =
      8 * e ^ 2 * (R ^ 4 * h₁ (R ^ 2) - R₀ ^ 4 * h₁ (R₀ ^ 2)) := by
  have hsq (r : ℝ) (hr : r ∈ Icc R₀ R) : u₀ < r ^ 2 := by
    have := hr.1
    nlinarith
  have hq : ContinuousOn (fun r : ℝ => r ^ 2) (Icc R₀ R) := (continuous_id.pow 2).continuousOn
  have hmem : MapsTo (fun r : ℝ => r ^ 2) (Icc R₀ R) (Ioi u₀) := hsq
  have h₁c : ContinuousOn h₁ (Ioi u₀) :=
    fun u hu => (hh₁ u hu).continuousAt.continuousWithinAt
  have hc₁ := h₁c.comp hq hmem
  have hc₂ := hh₂.comp hq hmem
  have hcont : ContinuousOn (fun r : ℝ => r ^ 3 * generalContactRadialTrace e h₁ h₂ r)
      (Icc R₀ R) := by
    unfold generalContactRadialTrace
    exact (continuous_id.pow 3).continuousOn.mul
      ((continuousOn_const.mul hc₁).add ((continuousOn_const.mul hq).mul hc₂))
  have hint : IntervalIntegrable (fun r : ℝ => r ^ 3 * generalContactRadialTrace e h₁ h₂ r)
      volume R₀ R := ContinuousOn.intervalIntegrable_of_Icc hR hcont
  have hderiv : ∀ r ∈ uIcc R₀ R, HasDerivAt (generalContactFluxPrimitive e h₁)
      (r ^ 3 * generalContactRadialTrace e h₁ h₂ r) r := by
    intro r hr
    rw [uIcc_of_le hR] at hr
    exact generalContactFluxPrimitive_hasDeriv hh₁ e r (hsq r hr)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold generalContactFluxPrimitive
  ring

def momentumAnnulus (R₀ R : ℝ) : Set DiracMomentum :=
  {k | R₀ < ‖k‖ ∧ ‖k‖ < R}

theorem measurableSet_momentumAnnulus (R₀ R : ℝ) : MeasurableSet (momentumAnnulus R₀ R) :=
  (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet

/-- The actual Hessian has the source's exact finite-annulus flux. -/
theorem generalContactDifference_flux {h h₁ h₂ : ℝ → ℝ} {u₀ R₀ R : ℝ}
    (hh : ∀ u, u₀ < u → HasDerivAt h (h₁ u) u)
    (hh₁ : ∀ u, u₀ < u → HasDerivAt h₁ (h₂ u) u)
    (hh₂ : ContinuousOn h₂ (Ioi u₀)) (hR₀ : 0 < R₀) (hbase : u₀ < R₀ ^ 2)
    (hR : R₀ ≤ R) (e : ℝ) :
    (2 * Real.pi) ^ (-4 : ℤ) * (∫ k : DiracMomentum in momentumAnnulus R₀ R,
      ∑ μ, generalContactDifference h e k μ μ) =
      e ^ 2 / Real.pi ^ 2 * (R ^ 4 * h₁ (R ^ 2) - R₀ ^ 4 * h₁ (R₀ ^ 2)) := by
  have hsq (k : DiracMomentum) (hk : k ∈ momentumAnnulus R₀ R) : u₀ < ‖k‖ ^ 2 := by
    have := hk.1
    have := norm_nonneg k
    nlinarith
  have heq : (∫ k : DiracMomentum in momentumAnnulus R₀ R,
      ∑ μ, generalContactDifference h e k μ μ) =
      ∫ k : DiracMomentum in momentumAnnulus R₀ R, generalContactRadialTrace e h₁ h₂ ‖k‖ := by
    apply setIntegral_congr_fun (measurableSet_momentumAnnulus R₀ R)
    intro k hk
    exact generalContactDifference_trace hh hh₁ e k (hsq k hk)
  rw [heq]
  have hp := fourier_radial_integral ((Ioo R₀ R).indicator (generalContactRadialTrace e h₁ h₂))
  have hl : (fun q : ScalarMomentum =>
      (Ioo R₀ R).indicator (generalContactRadialTrace e h₁ h₂) ‖q‖) =
      (momentumAnnulus R₀ R).indicator (fun q => generalContactRadialTrace e h₁ h₂ ‖q‖) := by
    funext q
    simp only [indicator, momentumAnnulus, mem_Ioo, mem_setOf_eq]
  rw [hl, integral_indicator (measurableSet_momentumAnnulus R₀ R)] at hp
  have hr : (fun r : ℝ => r ^ 3 * (Ioo R₀ R).indicator (generalContactRadialTrace e h₁ h₂) r) =
      (Ioo R₀ R).indicator (fun r => r ^ 3 * generalContactRadialTrace e h₁ h₂ r) := by
    funext r
    by_cases hx : r ∈ Ioo R₀ R <;> simp [indicator, hx]
  have hsub : Ioo R₀ R ⊆ Ioi (0 : ℝ) := fun r hr => hR₀.trans hr.1
  rw [hr, integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_self_of_subset_left hsub, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hR,
    generalContact_flux_interval hh₁ hh₂ hR₀ hbase hR e] at hp
  convert hp using 1
  field_simp [Real.pi_ne_zero]

/-- An integrable inverse-square derivative bound prevents escape to infinity;
    this proof needs no monotonicity of the original potential. -/
theorem not_tendsto_atTop_of_inverse_square_derivative_bound
    {h h₁ : ℝ → ℝ} {U C : ℝ} (hU : 0 < U) (hC : 0 ≤ C)
    (hh : ∀ u, U ≤ u → HasDerivAt h (h₁ u) u)
    (hbound : ∀ u, U ≤ u → |h₁ u| ≤ C / u ^ 2) :
    ¬ Tendsto h atTop atTop := by
  let g : ℝ → ℝ := fun u => h u + C / u
  have hderiv (u : ℝ) (hu : U ≤ u) : HasDerivAt g (h₁ u - C / u ^ 2) u := by
    have hne : u ≠ 0 := (hU.trans_le hu).ne'
    have hi := (hasDerivAt_const u C).fun_div (hasDerivAt_id u) hne
    convert (hh u hu).fun_add hi using 1
    simp only [id_eq, zero_mul, mul_one, zero_sub]
    ring
  have hnonpos (u : ℝ) (hu : U ≤ u) : h₁ u - C / u ^ 2 ≤ 0 :=
    sub_nonpos.mpr ((le_abs_self _).trans (hbound u hu))
  have hcont : ContinuousOn g (Ici U) :=
    fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ g (interior (Ici U)) :=
    fun u hu => (hderiv u (interior_subset hu)).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn g (Ici U) :=
    antitoneOn_of_deriv_nonpos (convex_Ici U) hcont hdiff (fun u hu => by
      rw [(hderiv u (interior_subset hu)).deriv]
      exact hnonpos u (interior_subset hu))
  have hupper (u : ℝ) (hu : U ≤ u) : h u ≤ h U + C / U := by
    have hg := hanti (mem_Ici.mpr (le_refl U)) (mem_Ici.mpr hu) hu
    have hc : 0 ≤ C / u := div_nonneg hC (hU.trans_le hu).le
    dsimp only [g] at hg
    linarith
  intro ht
  have he := ht.eventually (eventually_gt_atTop (h U + C / U))
  obtain ⟨u, hu, hlarge⟩ := (eventually_ge_atTop U |>.and he).exists
  exact (not_lt_of_ge (hupper u hu)) hlarge

def momentumExterior (R₀ : ℝ) : Set DiracMomentum := {k | R₀ < ‖k‖}

theorem contact_flux_bounded_of_integrable_trace {h h₁ h₂ : ℝ → ℝ} {u₀ R₀ e : ℝ}
    (hh : ∀ u, u₀ < u → HasDerivAt h (h₁ u) u)
    (hh₁ : ∀ u, u₀ < u → HasDerivAt h₁ (h₂ u) u)
    (hh₂ : ContinuousOn h₂ (Ioi u₀)) (hR₀ : 0 < R₀) (hbase : u₀ < R₀ ^ 2)
    (he : e ≠ 0)
    (hi : IntegrableOn (fun k : DiracMomentum => ∑ μ, generalContactDifference h e k μ μ)
      (momentumExterior R₀)) :
    ∃ K ≥ 0, ∀ R, R₀ ≤ R → |R ^ 4 * h₁ (R ^ 2) - R₀ ^ 4 * h₁ (R₀ ^ 2)| ≤ K := by
  let J : DiracMomentum → ℝ := fun k => ∑ μ, generalContactDifference h e k μ μ
  let W : ℝ := (2 * Real.pi) ^ (-4 : ℤ)
  let A : ℝ := e ^ 2 / Real.pi ^ 2
  let B : ℝ := ∫ k : DiracMomentum in momentumExterior R₀, |J k|
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 ≤ B := integral_nonneg (fun _ => abs_nonneg _)
  refine ⟨W * B / A, by positivity, ?_⟩
  intro R hR
  have hnorm : IntegrableOn (fun k : DiracMomentum => |J k|) (momentumExterior R₀) := by
    simpa only [Real.norm_eq_abs] using hi.norm
  have hmono : (∫ k : DiracMomentum in momentumAnnulus R₀ R, |J k|) ≤ B :=
    setIntegral_mono_set hnorm (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall fun k hk => hk.1)
  have habs : |∫ k : DiracMomentum in momentumAnnulus R₀ R, J k| ≤ B := by
    have hn : |∫ k : DiracMomentum in momentumAnnulus R₀ R, J k| ≤
        ∫ k : DiracMomentum in momentumAnnulus R₀ R, |J k| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := volume.restrict (momentumAnnulus R₀ R)) J)
    exact hn.trans hmono
  have hflux := generalContactDifference_flux hh hh₁ hh₂ hR₀ hbase hR e
  change W * (∫ k : DiracMomentum in momentumAnnulus R₀ R, J k) =
    A * (R ^ 4 * h₁ (R ^ 2) - R₀ ^ 4 * h₁ (R₀ ^ 2)) at hflux
  have hfluxAbs := congrArg abs hflux
  rw [abs_mul, abs_of_nonneg hW, abs_mul, abs_of_pos hA] at hfluxAbs
  have hmul := mul_le_mul_of_nonneg_left habs hW
  rw [hfluxAbs] at hmul
  apply (le_div_iff₀ hA).mpr
  simpa only [mul_comm] using hmul

theorem inverse_square_bound_of_contact_flux {h₁ : ℝ → ℝ} {R₀ K : ℝ}
    (hR₀ : 0 < R₀) (hK : 0 ≤ K)
    (hb : ∀ R, R₀ ≤ R → |R ^ 4 * h₁ (R ^ 2) - R₀ ^ 4 * h₁ (R₀ ^ 2)| ≤ K) :
    ∃ C ≥ 0, ∀ u, R₀ ^ 2 ≤ u → |h₁ u| ≤ C / u ^ 2 := by
  let P := R₀ ^ 4 * h₁ (R₀ ^ 2)
  refine ⟨K + |P|, by positivity, ?_⟩
  intro u hu
  have hu0 : 0 ≤ u := (sq_nonneg R₀).trans hu
  have hup : 0 < u := (sq_pos_of_pos hR₀).trans_le hu
  have hr : R₀ ≤ Real.sqrt u := by
    have h := Real.sqrt_le_sqrt hu
    simpa only [Real.sqrt_sq hR₀.le] using h
  have h := hb (Real.sqrt u) hr
  have hsq := Real.sq_sqrt hu0
  have hfour : Real.sqrt u ^ 4 = u ^ 2 := by
    calc
      _ = (Real.sqrt u ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsq]
  rw [hfour, hsq] at h
  have hwhole : |u ^ 2 * h₁ u| ≤ K + |P| := by
    calc
      _ = |(u ^ 2 * h₁ u - P) + P| := by rw [sub_add_cancel]
      _ ≤ |u ^ 2 * h₁ u - P| + |P| := abs_add_le _ _
      _ ≤ _ := add_le_add_right h _
  rw [abs_mul, abs_of_nonneg (sq_nonneg u)] at hwhole
  apply (le_div_iff₀ (sq_pos_of_pos hup)).mpr
  simpa only [mul_comm] using hwhole

/-- The actual radial Hessian trace cannot be absolutely integrable on the
    exterior when its potential tends to positive infinity. -/
theorem generalContactDifference_trace_not_integrable
    {h h₁ h₂ : ℝ → ℝ} {u₀ R₀ e : ℝ}
    (hh : ∀ u, u₀ < u → HasDerivAt h (h₁ u) u)
    (hh₁ : ∀ u, u₀ < u → HasDerivAt h₁ (h₂ u) u)
    (hh₂ : ContinuousOn h₂ (Ioi u₀)) (hR₀ : 0 < R₀) (hbase : u₀ < R₀ ^ 2)
    (he : e ≠ 0) (hlim : Tendsto h atTop atTop) :
    ¬ IntegrableOn (fun k : DiracMomentum => ∑ μ, generalContactDifference h e k μ μ)
      (momentumExterior R₀) := by
  intro hi
  obtain ⟨K, hK, hflux⟩ := contact_flux_bounded_of_integrable_trace hh hh₁ hh₂ hR₀ hbase he hi
  obtain ⟨C, hC, hbound⟩ := inverse_square_bound_of_contact_flux hR₀ hK hflux
  exact not_tendsto_atTop_of_inverse_square_derivative_bound (sq_pos_of_pos hR₀) hC
    (fun u hu => hh u (hbase.trans_le hu)) hbound hlim

theorem generalContactDifference_exists_nonintegrable_component
    {h h₁ h₂ : ℝ → ℝ} {u₀ R₀ e : ℝ}
    (hh : ∀ u, u₀ < u → HasDerivAt h (h₁ u) u)
    (hh₁ : ∀ u, u₀ < u → HasDerivAt h₁ (h₂ u) u)
    (hh₂ : ContinuousOn h₂ (Ioi u₀)) (hR₀ : 0 < R₀) (hbase : u₀ < R₀ ^ 2)
    (he : e ≠ 0) (hlim : Tendsto h atTop atTop) :
    ∃ μ, ¬ IntegrableOn (fun k : DiracMomentum => generalContactDifference h e k μ μ)
      (momentumExterior R₀) := by
  by_contra! hAll
  have hi : IntegrableOn (fun k : DiracMomentum => ∑ μ, generalContactDifference h e k μ μ)
      (momentumExterior R₀) := integrable_finset_sum _ (fun μ _ => hAll μ)
  exact generalContactDifference_trace_not_integrable hh hh₁ hh₂ hR₀ hbase he hlim hi

theorem radialDamperPotential_derivative_data {F : ℝ → ℝ} {u₀ : ℝ}
    (hF : ContDiffOn ℝ 2 F (Ioi u₀)) (hpos : ∀ u, u₀ < u → 0 < F u) :
    (∀ u, u₀ < u → HasDerivAt (radialDamperPotential F)
      (deriv (radialDamperPotential F) u) u) ∧
    (∀ u, u₀ < u → HasDerivAt (deriv (radialDamperPotential F))
      (deriv (deriv (radialDamperPotential F)) u) u) ∧
    ContinuousOn (deriv (deriv (radialDamperPotential F))) (Ioi u₀) := by
  have hc : ContDiffOn ℝ 2 (radialDamperPotential F) (Ioi u₀) :=
    (hF.log (fun u hu => (hpos u hu).ne')).neg
  have hc₁ : ContDiffOn ℝ 1 (deriv (radialDamperPotential F)) (Ioi u₀) :=
    hc.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hc₂ : ContDiffOn ℝ 0 (deriv (deriv (radialDamperPotential F))) (Ioi u₀) :=
    hc₁.deriv_of_isOpen isOpen_Ioi (by norm_num)
  refine ⟨?_, ?_, hc₂.continuousOn⟩
  · intro u hu
    exact ((hc.contDiffAt (Ioi_mem_nhds hu)).differentiableAt (by norm_num)).hasDerivAt
  · intro u hu
    exact ((hc₁.contDiffAt (Ioi_mem_nhds hu)).differentiableAt (by norm_num)).hasDerivAt

theorem radialDamperPotential_tendsto {F : ℝ → ℝ} {u₀ : ℝ}
    (hpos : ∀ u, u₀ < u → 0 < F u) (hzero : Tendsto F atTop (𝓝 0)) :
    Tendsto (radialDamperPotential F) atTop atTop := by
  have hp : ∀ᶠ u : ℝ in atTop, F u ∈ Ioi 0 :=
    (eventually_gt_atTop u₀).mono (fun u hu => hpos u hu)
  have ht : Tendsto F atTop (𝓝[>] (0 : ℝ)) := tendsto_nhdsWithin_iff.mpr ⟨hzero, hp⟩
  have hl := Real.tendsto_log_nhdsGT_zero.comp ht
  simpa only [radialDamperPotential, Function.comp_def] using
    tendsto_neg_atBot_atTop.comp hl

/-- The source's decay and C-two assumptions themselves imply the
    nonintegrability of the actual radial negative-log Hessian. -/
theorem radialDamper_contact_exists_nonintegrable_component
    {F : ℝ → ℝ} {u₀ R₀ e : ℝ}
    (hF : ContDiffOn ℝ 2 F (Ioi u₀)) (hpos : ∀ u, u₀ < u → 0 < F u)
    (hzero : Tendsto F atTop (𝓝 0)) (hR₀ : 0 < R₀) (hbase : u₀ < R₀ ^ 2)
    (he : e ≠ 0) :
    ∃ μ, ¬ IntegrableOn (fun k : DiracMomentum =>
      generalContactDifference (radialDamperPotential F) e k μ μ) (momentumExterior R₀) := by
  obtain ⟨hh, hh₁, hh₂⟩ := radialDamperPotential_derivative_data hF hpos
  exact generalContactDifference_exists_nonintegrable_component hh hh₁ hh₂ hR₀ hbase he
    (radialDamperPotential_tendsto hpos hzero)

def radialMultiplierDiracSymbol (F : ℝ → ℝ) (m : ℝ) (k : DiracMomentum) : DiracMatrix :=
  (F (‖k‖ ^ 2) : ℂ)⁻¹ • freeDiracSymbol m k

def radialLogdetDifference (F : ℝ → ℝ) (m : ℝ) (k : DiracMomentum) : ℝ :=
  Real.log (Matrix.det (radialMultiplierDiracSymbol F m k)).re -
    Real.log (Matrix.det (freeDiracSymbol m k)).re

theorem radialMultiplierDiracSymbol_det (F : ℝ → ℝ) (m : ℝ) (k : DiracMomentum) :
    Matrix.det (radialMultiplierDiracSymbol F m k) =
      ((((F (‖k‖ ^ 2))⁻¹) ^ 4 * (‖k‖ ^ 2 + m ^ 2) ^ 2 : ℝ) : ℂ) := by
  simp only [radialMultiplierDiracSymbol, Matrix.det_smul, Fintype.card_fin, freeDiracSymbol_det]
  push_cast
  rfl

/-- Reference subtraction is an identity of actual finite matrix determinants. -/
theorem radialLogdetDifference_eq {F : ℝ → ℝ} {m : ℝ} (hm : 0 < m)
    (k : DiracMomentum) (hF : 0 < F (‖k‖ ^ 2)) :
    radialLogdetDifference F m k = 4 * radialDamperPotential F (‖k‖ ^ 2) := by
  unfold radialLogdetDifference radialDamperPotential
  rw [radialMultiplierDiracSymbol_det, freeDiracSymbol_det, Complex.ofReal_re, Complex.ofReal_re]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_inv, Real.log_pow]
  ring

theorem radialLogdetDifference_complexLog {F : ℝ → ℝ} {m : ℝ} (hm : 0 < m)
    (k : DiracMomentum) (hF : 0 < F (‖k‖ ^ 2)) :
    Complex.log (Matrix.det (radialMultiplierDiracSymbol F m k)) -
      Complex.log (Matrix.det (freeDiracSymbol m k)) = (radialLogdetDifference F m k : ℂ) := by
  unfold radialLogdetDifference
  rw [radialMultiplierDiracSymbol_det, freeDiracSymbol_det, Complex.ofReal_re, Complex.ofReal_re,
    ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log (by positivity), Complex.ofReal_sub]

def radialLogdetFirstPartial (F : ℝ → ℝ) (m e : ℝ) (k : DiracMomentum) (μ : Fin 4) : ℝ :=
  deriv (fun r : ℝ => radialLogdetDifference F m (k + e • (r • EuclideanSpace.single μ 1))) 0

/-- The actual mixed second variation of the reference-subtracted trace log
in a constant background. -/
def radialLogdetContactDifference (F : ℝ → ℝ) (m e : ℝ) (k : DiracMomentum) (μ ν : Fin 4) : ℝ :=
  deriv (fun r : ℝ => radialLogdetFirstPartial F m e (k + e • (r • EuclideanSpace.single ν 1)) μ) 0

theorem charged_shift_eq (k v : DiracMomentum) (e r : ℝ) :
    k + e • (r • v) = k + (e * r) • v := by module

theorem radialLogdetFirstPartial_hasDeriv {F h₁ : ℝ → ℝ} {u₀ m : ℝ}
    (hm : 0 < m) (hpos : ∀ u, u₀ < u → 0 < F u)
    (hh : ∀ u, u₀ < u → HasDerivAt (radialDamperPotential F) (h₁ u) u)
    (e : ℝ) (k : DiracMomentum) (hk : u₀ < ‖k‖ ^ 2) (μ : Fin 4) :
    HasDerivAt (fun r : ℝ => radialLogdetDifference F m
      (k + e • (r • EuclideanSpace.single μ 1)))
      (4 * e * (2 * h₁ (‖k‖ ^ 2) * k μ)) 0 := by
  have hd := radialPotential_direction_hasDeriv hh k hk μ
  have hd' : HasDerivAt
      (fun r : ℝ => radialDamperPotential F (‖k + r • EuclideanSpace.single μ 1‖ ^ 2))
      (2 * h₁ (‖k‖ ^ 2) * k μ) (e * 0) := by simpa only [mul_zero] using hd
  have hc : HasDerivAt (fun r : ℝ => e * r) e 0 := by
    simpa only [mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul e
  have hs := (hd'.comp 0 (h := fun r : ℝ => e * r) hc).const_mul 4
  have hs' : HasDerivAt
      (fun r : ℝ => 4 * radialDamperPotential F (‖k + e • (r • EuclideanSpace.single μ 1)‖ ^ 2))
      (4 * e * (2 * h₁ (‖k‖ ^ 2) * k μ)) 0 := by
    convert hs using 1
    · ext r
      simp only [charged_shift_eq, Function.comp_def]
    · ring
  have hnorm : Tendsto (fun r : ℝ => ‖k + e • (r • EuclideanSpace.single μ 1)‖ ^ 2)
      (𝓝 0) (𝓝 (‖k‖ ^ 2)) := by
    have hcont : Continuous (fun r : ℝ => ‖k + e • (r • EuclideanSpace.single μ 1)‖ ^ 2) := by fun_prop
    simpa only [zero_smul, smul_zero, add_zero] using hcont.continuousAt.tendsto (x := 0)
  have heq : (fun r : ℝ => radialLogdetDifference F m (k + e • (r • EuclideanSpace.single μ 1))) =ᶠ[𝓝 0]
      (fun r : ℝ => 4 * radialDamperPotential F (‖k + e • (r • EuclideanSpace.single μ 1)‖ ^ 2)) := by
    filter_upwards [hnorm.eventually (Ioi_mem_nhds hk)] with r hr
    exact radialLogdetDifference_eq hm _ (hpos _ hr)
  exact hs'.congr_of_eventuallyEq heq

theorem radialLogdetFirstPartial_eq {F h₁ : ℝ → ℝ} {u₀ m : ℝ}
    (hm : 0 < m) (hpos : ∀ u, u₀ < u → 0 < F u)
    (hh : ∀ u, u₀ < u → HasDerivAt (radialDamperPotential F) (h₁ u) u)
    (e : ℝ) (k : DiracMomentum) (hk : u₀ < ‖k‖ ^ 2) (μ : Fin 4) :
    radialLogdetFirstPartial F m e k μ = 4 * e * (2 * h₁ (‖k‖ ^ 2) * k μ) :=
  (radialLogdetFirstPartial_hasDeriv hm hpos hh e k hk μ).deriv

theorem radialLogdetContactDifference_eq_iterated_background
    (F : ℝ → ℝ) (m e : ℝ) (k : DiracMomentum) (μ ν : Fin 4) :
    radialLogdetContactDifference F m e k μ ν =
      deriv (fun h : ℝ => deriv (fun r : ℝ => radialLogdetDifference F m
        (k + e • (h • EuclideanSpace.single ν 1 + r • EuclideanSpace.single μ 1))) 0) 0 := by
  unfold radialLogdetContactDifference radialLogdetFirstPartial
  congr 1
  funext h
  congr 1
  funext r
  congr 1
  module

/-- The raw difference is derived from actual finite matrix trace-log
    differentiation, giving the source's radial Hessian without assuming it. -/
theorem radialLogdetContactDifference_eq {F h₁ h₂ : ℝ → ℝ} {u₀ m : ℝ}
    (hm : 0 < m) (hpos : ∀ u, u₀ < u → 0 < F u)
    (hh : ∀ u, u₀ < u → HasDerivAt (radialDamperPotential F) (h₁ u) u)
    (hh₁ : ∀ u, u₀ < u → HasDerivAt h₁ (h₂ u) u)
    (e : ℝ) (k : DiracMomentum) (hk : u₀ < ‖k‖ ^ 2) (μ ν : Fin 4) :
    radialLogdetContactDifference F m e k μ ν =
      generalContactDifference (radialDamperPotential F) e k μ ν := by
  let H : ℝ := 2 * h₁ (‖k‖ ^ 2) * (if μ = ν then 1 else 0) +
    4 * h₂ (‖k‖ ^ 2) * k μ * k ν
  have hd := radialGradient_direction_hasDeriv hh₁ k hk μ ν
  have hd' : HasDerivAt
      (fun r : ℝ => 2 * h₁ (‖k + r • EuclideanSpace.single ν 1‖ ^ 2) *
        (k + r • EuclideanSpace.single ν (1 : ℝ) : DiracMomentum) μ) H (e * 0) := by
    simpa only [mul_zero] using hd
  have hc : HasDerivAt (fun r : ℝ => e * r) e 0 := by
    simpa only [mul_one] using (hasDerivAt_id (0 : ℝ)).const_mul e
  have hs := (hd'.comp 0 (h := fun r : ℝ => e * r) hc).const_mul (4 * e)
  have hs' : HasDerivAt
      (fun r : ℝ => 4 * e * (2 * h₁ (‖k + e • (r • EuclideanSpace.single ν 1)‖ ^ 2) *
        (k + e • (r • EuclideanSpace.single ν 1) : DiracMomentum) μ)) (4 * e ^ 2 * H) 0 := by
    convert hs using 1
    · ext r
      simp only [charged_shift_eq, Function.comp_def]
    · ring
  have hnorm : Tendsto (fun r : ℝ => ‖k + e • (r • EuclideanSpace.single ν 1)‖ ^ 2)
      (𝓝 0) (𝓝 (‖k‖ ^ 2)) := by
    have hcont : Continuous (fun r : ℝ => ‖k + e • (r • EuclideanSpace.single ν 1)‖ ^ 2) := by fun_prop
    simpa only [zero_smul, smul_zero, add_zero] using hcont.continuousAt.tendsto (x := 0)
  have heq : (fun r : ℝ => radialLogdetFirstPartial F m e
      (k + e • (r • EuclideanSpace.single ν 1)) μ) =ᶠ[𝓝 0]
      (fun r : ℝ => 4 * e * (2 * h₁ (‖k + e • (r • EuclideanSpace.single ν 1)‖ ^ 2) *
        (k + e • (r • EuclideanSpace.single ν 1) : DiracMomentum) μ)) := by
    filter_upwards [hnorm.eventually (Ioi_mem_nhds hk)] with r hr
    exact radialLogdetFirstPartial_eq hm hpos hh e _ hr μ
  unfold radialLogdetContactDifference generalContactDifference
  rw [radialScalarHessian_eq hh hh₁ k hk]
  exact (hs'.congr_of_eventuallyEq heq).deriv

/-- The principal assertion of cor:OQED-general-contact-obstruction, on the
    actual reference-subtracted constant-background trace-log coefficient. -/
theorem radialLogdetContactDifference_exists_nonintegrable_component
    {F : ℝ → ℝ} {u₀ R₀ m e : ℝ}
    (hF : ContDiffOn ℝ 2 F (Ioi u₀)) (hpos : ∀ u, u₀ < u → 0 < F u)
    (hzero : Tendsto F atTop (𝓝 0)) (hR₀ : 0 < R₀) (hbase : u₀ < R₀ ^ 2)
    (hm : 0 < m) (he : e ≠ 0) :
    ∃ μ, ¬ IntegrableOn (fun k : DiracMomentum => radialLogdetContactDifference F m e k μ μ)
      (momentumExterior R₀) := by
  obtain ⟨hh, hh₁, _⟩ := radialDamperPotential_derivative_data hF hpos
  obtain ⟨μ, hbad⟩ := radialDamper_contact_exists_nonintegrable_component hF hpos hzero hR₀ hbase he
  refine ⟨μ, ?_⟩
  intro hi
  apply hbad
  apply hi.congr
  filter_upwards [ae_restrict_mem (isOpen_lt continuous_const continuous_norm).measurableSet] with k hk
  have hsq : u₀ < ‖k‖ ^ 2 := by
    have := norm_nonneg k
    change R₀ < ‖k‖ at hk
    nlinarith
  exact radialLogdetContactDifference_eq hm hpos hh hh₁ e k hsq μ μ

/-- The exact Fourier-normalized source flux for the reference-subtracted
    coefficient generated by the actual finite matrix determinants. -/
theorem radialLogdetContactDifference_flux {F : ℝ → ℝ} {u₀ R₀ R m : ℝ}
    (hF : ContDiffOn ℝ 2 F (Ioi u₀)) (hpos : ∀ u, u₀ < u → 0 < F u)
    (hm : 0 < m) (hR₀ : 0 < R₀) (hbase : u₀ < R₀ ^ 2) (hR : R₀ ≤ R) (e : ℝ) :
    (2 * Real.pi) ^ (-4 : ℤ) * (∫ k : DiracMomentum in momentumAnnulus R₀ R,
      ∑ μ, radialLogdetContactDifference F m e k μ μ) =
      e ^ 2 / Real.pi ^ 2 *
        (R ^ 4 * deriv (radialDamperPotential F) (R ^ 2) -
          R₀ ^ 4 * deriv (radialDamperPotential F) (R₀ ^ 2)) := by
  obtain ⟨hh, hh₁, hh₂⟩ := radialDamperPotential_derivative_data hF hpos
  have heq : (∫ k : DiracMomentum in momentumAnnulus R₀ R,
      ∑ μ, radialLogdetContactDifference F m e k μ μ) =
      ∫ k : DiracMomentum in momentumAnnulus R₀ R,
        ∑ μ, generalContactDifference (radialDamperPotential F) e k μ μ := by
    apply setIntegral_congr_fun (measurableSet_momentumAnnulus R₀ R)
    intro k hk
    apply Finset.sum_congr rfl
    intro μ _
    have hsq : u₀ < ‖k‖ ^ 2 := by
      have := hk.1
      have := norm_nonneg k
      nlinarith
    exact radialLogdetContactDifference_eq hm hpos hh hh₁ e k hsq μ μ
  rw [heq]
  exact generalContactDifference_flux hh hh₁ hh₂ hR₀ hbase hR e

end UV
