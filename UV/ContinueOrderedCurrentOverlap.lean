import UV.ContinueOrderedCurrentPlane
import UV.ContinueOmegaResultHolonomy

/-! Frequency integration of the actual signed temporal Wilson currents.
The result is their carrier-time overlap, with each individual segment's
positive diagonal term retained. -/

noncomputable section

open MeasureTheory Finset Set
open scoped ComplexConjugate

namespace UV.SectorPlane.OrderedTwoBandPath

private theorem pulse_anchor_primitive (ω a b : ℝ) :
    (∫ t in a..b, Complex.exp (Complex.I*(ω:ℂ)*(t:ℂ))) =
      Complex.exp (Complex.I*(ω:ℂ)*(a:ℂ)) * omegaRotorMark (b-a) (-ω) := by
  let F := fun t : ℝ => Complex.exp (Complex.I*(ω:ℂ)*(t:ℂ))
  have h := intervalIntegral.integral_comp_add_left (a := (0:ℝ)) (b := b-a) F a
  simp only [add_zero,add_sub_cancel] at h
  rw [←h]
  unfold omegaRotorMark
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [F,normalAngularPhase]
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem pulse_anchor_difference (P : OrderedTwoBandPath) (j : ℕ) (ω a : ℝ) :
    P.pulse j ω = Complex.exp (Complex.I*(ω:ℂ)*(a:ℂ)) *
      (omegaRotorMark (P.time (j+1)-a) (-ω)-omegaRotorMark (P.time j-a) (-ω)) := by
  let F := fun t : ℝ => Complex.exp (Complex.I*(ω:ℂ)*(t:ℂ))
  have hc : Continuous F := by unfold F; fun_prop
  have he := intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := volume) a (P.time (j+1)))
    (hc.intervalIntegrable (μ := volume) a (P.time j))
  change (∫ t in P.time j..P.time (j+1), F t) = _
  rw [←he]
  simp only [F,pulse_anchor_primitive, mul_sub]

/-- If both intervals point forward, this is the length of their overlap.
Swapping either interval's endpoints reverses the sign. -/
def signedOverlap (b₀ b₁ c₀ c₁ : ℝ) : ℝ :=
  min b₁ c₁ - min b₁ c₀ - min b₀ c₁ + min b₀ c₀

theorem pulse_pair_covariance (P R : OrderedTwoBandPath) (j k : ℕ) :
    Integrable (fun ω => P.pulse j ω*R.pulse k (-ω)) ∧
    ((2*Real.pi:ℝ):ℂ)⁻¹ * (∫ ω, P.pulse j ω*R.pulse k (-ω)) =
      (signedOverlap (P.time j) (P.time (j+1)) (R.time k) (R.time (k+1)):ℂ) := by
  let b₀ := P.time j
  let b₁ := P.time (j+1)
  let c₀ := R.time k
  let c₁ := R.time (k+1)
  let a := min (min b₀ b₁) (min c₀ c₁)
  have h₀ : 0 ≤ b₀-a := sub_nonneg.mpr ((min_le_left _ _).trans (min_le_left _ _))
  have h₁ : 0 ≤ b₁-a := sub_nonneg.mpr ((min_le_left _ _).trans (min_le_right _ _))
  have k₀ : 0 ≤ c₀-a := sub_nonneg.mpr ((min_le_right _ _).trans (min_le_left _ _))
  have k₁ : 0 ≤ c₁-a := sub_nonneg.mpr ((min_le_right _ _).trans (min_le_right _ _))
  let G := fun b c (ω : ℝ) => omegaRotorMark (b-a) (-ω)*omegaRotorMark (c-a) ω
  have hG {b c : ℝ} (hb : 0 ≤ b-a) (hc : 0 ≤ c-a) : Integrable (G b c) :=
    (omega_rotor_pair_integrable hb hc (le_max_left _ _) (le_max_right _ _)).1
  have hcov {b c : ℝ} (hb : 0 ≤ b-a) (hc : 0 ≤ c-a) :
      ((2*Real.pi:ℝ):ℂ)⁻¹ * (∫ ω, G b c ω) = ((min b c-a : ℝ):ℂ) := by
    have h := omega_rotor_pair_covariance hb hc
    simpa only [min_sub_sub_right] using h
  have eqv (ω : ℝ) : P.pulse j ω*R.pulse k (-ω) =
      G b₁ c₁ ω-G b₁ c₀ ω-G b₀ c₁ ω+G b₀ c₀ ω := by
    rw [P.pulse_anchor_difference j ω a,R.pulse_anchor_difference k (-ω) a]
    simp only [neg_neg,Complex.ofReal_neg,G,b₀,b₁,c₀,c₁]
    rw [show Complex.I*(-(ω:ℂ))*(a:ℂ) = -(Complex.I*(ω:ℂ)*(a:ℂ)) by ring,
      mul_mul_mul_comm,←Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_mul]
    ring
  simp only [eqv]
  have hab : Integrable (fun ω => G b₁ c₁ ω - G b₁ c₀ ω) := (hG h₁ k₁).sub (hG h₁ k₀)
  have habc : Integrable (fun ω => G b₁ c₁ ω - G b₁ c₀ ω - G b₀ c₁ ω) := hab.sub (hG h₀ k₁)
  refine ⟨habc.add (hG h₀ k₀),?_⟩
  rw [integral_add habc (hG h₀ k₀),integral_sub hab (hG h₀ k₁),integral_sub (hG h₁ k₁) (hG h₁ k₀),
    mul_add,mul_sub,mul_sub,hcov h₁ k₁,hcov h₁ k₀,hcov h₀ k₁,hcov h₀ k₀]
  simp only [signedOverlap,Complex.ofReal_add,Complex.ofReal_sub,b₀,b₁,c₀,c₁]
  ring

theorem overlap_self (x y : ℝ) : signedOverlap x y x y = |y-x| := by
  rcases le_total x y with h|h
  · simp [signedOverlap,h,abs_of_nonneg (sub_nonneg.mpr h)]
  · simp [signedOverlap,h,abs_of_nonpos (sub_nonpos.mpr h)]; ring

/-- The same-link self-contraction has its full (unsigned) duration. -/
theorem pulse_self_covariance (P : OrderedTwoBandPath) (j : ℕ) :
    ((2*Real.pi:ℝ):ℂ)⁻¹ * (∫ ω, P.pulse j ω*P.pulse j (-ω)) = ((|P.duration j|:ℝ):ℂ) :=
  (P.pulse_pair_covariance P j j).2.trans (congrArg Complex.ofReal (overlap_self _ _))

/-- The complete density pairing includes every pair of links, including
diagonal self-pairs even when two currents are evaluated on the same path. -/
theorem density_pair_covariance (P R : OrderedTwoBandPath) (p : Spatial) :
    Integrable (fun ω => P.density ω p*R.density (-ω) (-p)) ∧
    ((2*Real.pi:ℝ):ℂ)⁻¹ * (∫ ω, P.density ω p*R.density (-ω) (-p)) =
      ∑ j ∈ range P.hops, ∑ k ∈ range R.hops,
        (spatialWave p (P.position j)*spatialWave (-p) (R.position k)) *
          (signedOverlap (P.time j) (P.time (j+1)) (R.time k) (R.time (k+1)):ℂ) := by
  let W := fun j k => spatialWave p (P.position j)*spatialWave (-p) (R.position k)
  let F := fun j k (ω : ℝ) => W j k * (P.pulse j ω*R.pulse k (-ω))
  have hF (j k : ℕ) : Integrable (F j k) := (P.pulse_pair_covariance R j k).1.const_mul _
  have eqv (ω : ℝ) : P.density ω p*R.density (-ω) (-p) =
      ∑ j ∈ range P.hops, ∑ k ∈ range R.hops, F j k ω := by
    rw [density,density,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    unfold F W
    exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => mul_mul_mul_comm _ _ _ _
  have hi (j : ℕ) : Integrable (fun ω => ∑ k ∈ range R.hops, F j k ω) := integrable_finset_sum _ (fun k _ => hF j k)
  simp only [eqv]
  refine ⟨integrable_finset_sum _ (fun j _ => hi j),?_⟩
  rw [integral_finset_sum _ (fun j _ => hi j),Finset.mul_sum]
  apply sum_congr rfl
  intro j _
  rw [integral_finset_sum _ (fun k _ => hF j k),Finset.mul_sum]
  apply sum_congr rfl
  intro k _
  simp only [F,integral_const_mul,mul_left_comm ((2*Real.pi:ℝ):ℂ)⁻¹ (W j k),
    (P.pulse_pair_covariance R j k).2,W]

end UV.SectorPlane.OrderedTwoBandPath
