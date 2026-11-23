import UV.ContinueGaugeRootDiagonal
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Identification of the spectral generator with the literal Landau
differential expression on every smooth, compactly supported test. -/

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ComplexConjugate
namespace UV.RootMagnetic

def realLandauMode (b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt (Real.sqrt (2*b) / Real.sqrt (2*Real.pi)) / factorialRoot n) * rootFiberMode b n x

theorem real_mode_smooth (b : ℝ) (n : ℕ) :
    ContDiff ℝ ⊤ (realLandauMode b n) := by
  have hp : ContDiff ℝ ⊤ (fun x : ℝ => (rootHermite n).eval x) := by
    generalize rootHermite n = P
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
    | monomial k c =>
        simpa only [Polynomial.eval_monomial] using (contDiff_const.mul
          (contDiff_id.pow k) : ContDiff ℝ ⊤ (fun x : ℝ => c*x^k))
  have hq : ContDiff ℝ ⊤ (fun x : ℝ => Real.sqrt (2*b)*x) := by fun_prop
  have he : ContDiff ℝ ⊤ (fun x : ℝ => Real.exp (-b*x^2/2)) := by fun_prop
  exact contDiff_const.mul ((hp.comp hq).mul he)

private theorem real_mode_eigen {b : ℝ} (hb : 0 < b) (n : ℕ) (x : ℝ) :
    -(deriv (deriv (realLandauMode b n)) x) + (b*x)^2 * realLandauMode b n x =
      landauLevel b n * realLandauMode b n x := by
  unfold realLandauMode landauLevel
  simp only [deriv_const_mul_field']
  linear_combination (Real.sqrt (Real.sqrt (2*b) / Real.sqrt (2*Real.pi)) / factorialRoot n) *
    rootFiberMode_eigen b hb n x

def landauDifferential (b : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -deriv (deriv f) x + ((b*x)^2 : ℝ) * f x

private theorem continuous_integrable_product {u v : ℝ → ℂ}
    (hu : Continuous u) (hv : Continuous v) (hs : HasCompactSupport v) :
    Integrable (u*v) :=
  (hu.mul hv).integrable_of_hasCompactSupport hs.mul_left

private theorem landau_mode_test_identity {b : ℝ} (hb : 0 < b) (n : ℕ)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    (∫ x, normalizedLandauMode b n x * landauDifferential b f x) =
      (landauLevel b n : ℂ) * ∫ x, normalizedLandauMode b n x * f x := by
  let u := realLandauMode b n
  let g := normalizedLandauMode b n
  let g₁ : ℝ → ℂ := fun x => ((deriv u x : ℝ) : ℂ)
  let g₂ : ℝ → ℂ := fun x => ((deriv (deriv u) x : ℝ) : ℂ)
  have hU : ContDiff ℝ 2 u := (real_mode_smooth b n).of_le le_top
  have hU₁ : ContDiff ℝ 1 (deriv u) := hU.deriv'
  have hU₂ : Continuous (deriv (deriv u)) := (hU₁.deriv' : ContDiff ℝ 0 _).continuous
  have hF₁ : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hF₂ : Continuous (deriv (deriv f)) := (hF₁.deriv' : ContDiff ℝ 0 _).continuous
  have hG : Continuous g := Complex.continuous_ofReal.comp hU.continuous
  have hG₁ : Continuous g₁ := Complex.continuous_ofReal.comp hU₁.continuous
  have hG₂ : Continuous g₂ := Complex.continuous_ofReal.comp hU₂
  have hd (x : ℝ) : HasDerivAt g (g₁ x) x :=
    ((hU.differentiable (by norm_num)).differentiableAt.hasDerivAt (x := x)).ofReal_comp
  have hd₁ (x : ℝ) : HasDerivAt g₁ (g₂ x) x :=
    ((hU₁.differentiable (by norm_num)).differentiableAt.hasDerivAt (x := x)).ofReal_comp
  have ibp₀ := integral_mul_deriv_eq_deriv_mul_of_integrable hd
    (fun x => (hF₁.differentiable (by norm_num)).differentiableAt.hasDerivAt (x := x))
    (continuous_integrable_product hG hF₂ hs.deriv.deriv)
    (continuous_integrable_product hG₁ hF₁.continuous hs.deriv)
    (continuous_integrable_product hG hF₁.continuous hs.deriv)
  have ibp₁ := integral_mul_deriv_eq_deriv_mul_of_integrable hd₁
    (fun x => (hf.differentiable (by norm_num)).differentiableAt.hasDerivAt (x := x))
    (continuous_integrable_product hG₁ hF₁.continuous hs.deriv)
    (continuous_integrable_product hG₂ hf.continuous hs)
    (continuous_integrable_product hG₁ hf.continuous hs)
  let V : ℝ → ℂ := fun x => (((b*x)^2 : ℝ) : ℂ)
  have hV : Continuous V := by dsimp [V]; fun_prop
  have hmain (x : ℝ) : -g₂ x + V x*g x = (landauLevel b n : ℂ)*g x := by
    change (-((deriv (deriv u) x : ℝ) : ℂ) + (((b*x)^2 : ℝ) : ℂ)*((u x : ℝ) : ℂ)) =
      (landauLevel b n : ℂ)*((u x : ℝ) : ℂ)
    exact_mod_cast (real_mode_eigen hb n x)
  calc
    _ = (-(∫ x, g x * deriv (deriv f) x)) + ∫ x, g x * (V x * f x) := by
      change (∫ x, g x * (- deriv (deriv f) x + V x * f x)) = _
      have hpt (x : ℝ) : g x * (- deriv (deriv f) x + V x * f x) =
          (-(g * deriv (deriv f)) + g * (V * f)) x := by simp [mul_add]
      simp_rw [hpt]
      have hi₁ := (continuous_integrable_product hG hF₂ hs.deriv.deriv).neg
      have hi₂ : Integrable (g*(V*f)) := continuous_integrable_product hG (hV.mul hf.continuous) hs.mul_left
      exact (integral_add hi₁ hi₂).trans (by simp only [Pi.neg_apply, Pi.mul_apply, integral_neg])
    _ = (-(∫ x, g₂ x * f x)) + ∫ x, (V x*g x) * f x := by
      rw [ibp₀, ibp₁, neg_neg]
      congr 1
      apply integral_congr_ae (Eventually.of_forall fun x => by ring)
    _ = ∫ x, (-g₂ x + V x*g x) * f x := by
      have hpt (x : ℝ) : (-g₂ x + V x*g x) * f x =
          (-(g₂ * f) + (V*g) * f) x := by simp [add_mul]
      simp_rw [hpt]
      have hi₁ := (continuous_integrable_product hG₂ hf.continuous hs).neg
      have hi₂ : Integrable (V*g*f) := continuous_integrable_product (hV.mul hG) hf.continuous hs
      exact ((integral_add hi₁ hi₂).trans (by simp only [Pi.neg_apply, Pi.mul_apply, integral_neg])).symm
    _ = _ := by
      simp_rw [hmain, mul_assoc]
      rw [integral_const_mul]

/-- This self-adjoint realization has the normalized Landau eigenbasis and
agrees with the original differential operator on every compact smooth
test. The conclusion includes its actual graph membership. -/
theorem magnetic_fiber_operator {b : ℝ} (hb : 0 < b) :
    ∃ (B : HilbertBasis ℕ ℂ LebesgueFiber) (H : LebesgueFiber →ₗ.[ℂ] LebesgueFiber),
      IsSelfAdjoint H ∧ (∀ n, ⇑(B n) =ᵐ[volume] normalizedLandauMode b n) ∧
      (∀ f g : LebesgueFiber, (f,g) ∈ H.graph ↔
        ∀ n, ⟪B n,g⟫_ℂ = (landauLevel b n : ℂ) * ⟪B n,f⟫_ℂ) ∧
      ∀ (f : ℝ → ℂ) (_ : ContDiff ℝ 2 f) (_ : HasCompactSupport f),
        ∃ v w : LebesgueFiber, ⇑v =ᵐ[volume] f ∧ ⇑w =ᵐ[volume] landauDifferential b f ∧ (v,w) ∈ H.graph := by
  obtain ⟨B,H,hH,hB,hGraph⟩ := magnetic_fiber_spectral_graph hb
  refine ⟨B,H,hH,hB,hGraph,fun f hf hs => ?_⟩
  have hF₁ : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hF₂ : Continuous (deriv (deriv f)) := (hF₁.deriv' : ContDiff ℝ 0 _).continuous
  have hf₀ : MemLp f 2 (volume : Measure ℝ) := hf.continuous.memLp_of_hasCompactSupport hs
  have hgC : Continuous (landauDifferential b f) := by
    have hfC := hf.continuous
    unfold landauDifferential
    fun_prop
  have hgS : HasCompactSupport (landauDifferential b f) := hs.deriv.deriv.neg.add hs.mul_left
  have hg₀ : MemLp (landauDifferential b f) 2 (volume : Measure ℝ) :=
    hgC.memLp_of_hasCompactSupport hgS
  let v := hf₀.toLp f
  let w := hg₀.toLp (landauDifferential b f)
  have innerTest (n : ℕ) (x : LebesgueFiber) (g : ℝ → ℂ) (hg : ⇑x =ᵐ[volume] g) :
      ⟪B n,x⟫_ℂ = ∫ y, normalizedLandauMode b n y * g y := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hB n,hg] with y h₁ h₂
    rw [h₁,h₂,RCLike.inner_apply]
    change g y * conj ((realLandauMode b n y : ℝ) : ℂ) = _
    rw [Complex.conj_ofReal]
    exact mul_comm _ _
  refine ⟨v,w,hf₀.coeFn_toLp,hg₀.coeFn_toLp,(hGraph v w).2 fun n => ?_⟩
  rw [innerTest n v f hf₀.coeFn_toLp, innerTest n w _ hg₀.coeFn_toLp]
  exact landau_mode_test_identity hb n f hf hs

end UV.RootMagnetic
