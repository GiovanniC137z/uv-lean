import UV.StableMomentThreshold
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Explicit pole parameters and the continuum boundary values of the positive
bulk comparison in the revised manuscript. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace UV.RevisionSpectrum

def bulkKappa (β b M₂ : ℝ) : ℝ := (Real.sqrt (β^2 + 4*(M₂-b)) - β)/2

def bulkPole (β b M₂ : ℝ) : ℝ := M₂ - bulkKappa β b M₂ ^ 2

def bulkResidue (β b M₂ : ℝ) : ℝ := (1+β/(2*bulkKappa β b M₂))⁻¹

theorem bulkKappa_sq_add {β b M₂ : ℝ} (hb : b < M₂) :
    bulkKappa β b M₂ ^ 2 + β * bulkKappa β b M₂ = M₂-b := by
  have h := Real.sq_sqrt (show 0 ≤ β^2 + 4*(M₂-b) by nlinarith)
  unfold bulkKappa
  nlinarith

theorem bulkKappa_pos {β b M₂ : ℝ} (hβ : 0 < β) (hb : b < M₂) :
    0 < bulkKappa β b M₂ := by
  have hsq := Real.sq_sqrt (show 0 ≤ β^2 + 4*(M₂-b) by nlinarith)
  have hpos := Real.sqrt_nonneg (β^2 + 4*(M₂-b))
  unfold bulkKappa
  by_contra! h
  have h' := (sq_le_sq₀ hpos hβ.le).mpr (show Real.sqrt (β^2 + 4*(M₂-b)) ≤ β by linarith)
  linarith

/-- The unique gap pole, including its exact placement above the boundary
mass and below the bulk threshold. -/
theorem bulkPole_unique {β b M₂ : ℝ} (hβ : 0 < β) (hb : b < M₂) :
    b < bulkPole β b M₂ ∧ bulkPole β b M₂ < M₂ ∧
    b - bulkPole β b M₂ + β * Real.sqrt (M₂ - bulkPole β b M₂) = 0 ∧
    ∀ s : ℝ, s ≤ M₂ → b - s + β * Real.sqrt (M₂ - s) = 0 → s = bulkPole β b M₂ := by
  have hk := bulkKappa_pos hβ hb
  have hq := bulkKappa_sq_add (β := β) hb
  have hsq : M₂ - bulkPole β b M₂ = bulkKappa β b M₂ ^ 2 := by unfold bulkPole; ring
  have hroot : Real.sqrt (M₂ - bulkPole β b M₂) = bulkKappa β b M₂ := by
    rw [hsq, Real.sqrt_sq hk.le]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold bulkPole
    nlinarith [mul_pos hβ hk]
  · linarith [sq_pos_of_pos hk]
  · rw [hroot]
    unfold bulkPole
    linarith
  · intro s hs hzero
    let u := Real.sqrt (M₂-s)
    have hu := Real.sqrt_nonneg (M₂-s)
    have hsquare := Real.sq_sqrt (sub_nonneg.mpr hs)
    have hMul : (u - bulkKappa β b M₂) * (u + bulkKappa β b M₂ + β) = 0 := by
      dsimp [u]
      nlinarith
    have heq := (mul_eq_zero.mp hMul).resolve_right (by dsimp [u]; positivity)
    unfold bulkPole
    change u^2 = M₂-s at hsquare
    have hu' : u = bulkKappa β b M₂ := sub_eq_zero.mp heq
    rw [hu'] at hsquare
    linarith

theorem bulkInverse_hasDerivAt_pole {β b M₂ : ℝ} (hβ : 0 < β) (hb : b < M₂) :
    HasDerivAt (fun x => x + b + β * Real.sqrt (x+M₂))
      (1+β/(2*bulkKappa β b M₂)) (-bulkPole β b M₂) := by
  have hk := bulkKappa_pos hβ hb
  have hs : -bulkPole β b M₂ + M₂ = bulkKappa β b M₂ ^ 2 := by unfold bulkPole; ring
  have hne : -bulkPole β b M₂ + M₂ ≠ 0 := by rw [hs]; positivity
  have hsq := (Real.hasDerivAt_sqrt hne).comp (-bulkPole β b M₂) ((hasDerivAt_id _).add_const M₂)
  simp only [id_eq, mul_one, hs, Real.sqrt_sq hk.le] at hsq
  simpa only [div_eq_mul_inv, one_mul, mul_one, Function.comp_apply, Pi.add_apply, id_eq] using
    (((hasDerivAt_id (-bulkPole β b M₂)).add_const b).add (hsq.const_mul β))

theorem bulkResidue_positive {β b M₂ : ℝ} (hβ : 0 < β) (hb : b < M₂) :
    0 < bulkResidue β b M₂ := by
  unfold bulkResidue
  have hk := bulkKappa_pos hβ hb
  positivity

def normalMode (β k t r : ℝ) : ℝ := Real.cos (k*r) + t/(β*k) * Real.sin (k*r)

def bulkBoundaryDensity (β k t : ℝ) : ℝ := β*k / (Real.pi*(t^2+(β*k)^2))

def bulkCutLayer (β k t r r' : ℝ) : ℂ :=
  Complex.exp ((↑(-(k*(r+r'))) : ℂ)*Complex.I) / ((t : ℂ) + (β*k : ℝ)*Complex.I) +
  (Complex.exp ((↑(-(k*|r-r'|)) : ℂ)*Complex.I) -
    Complex.exp ((↑(-(k*(r+r'))) : ℂ)*Complex.I)) / ((2*β*k : ℝ)*Complex.I)

/-- The continuum jump of the complete Green block includes the Dirichlet
term. Its density is the explicit rank-one outer product. -/
theorem bulkCutLayer_im {β k : ℝ} (hβ : 0 < β) (hk : 0 < k) (t r r' : ℝ) :
    -(bulkCutLayer β k t r r').im / Real.pi =
      bulkBoundaryDensity β k t * normalMode β k t r * normalMode β k t r' := by
  have hbk : 0 < β*k := mul_pos hβ hk
  have hep : 0 < t^2 + (β*k)^2 := by positivity
  have hπ := Real.pi_ne_zero
  by_cases hr : r' ≤ r
  · have hdiff : 0 ≤ r-r' := sub_nonneg.mpr hr
    unfold bulkCutLayer bulkBoundaryDensity normalMode
    simp only [Complex.add_im, Complex.sub_im, Complex.sub_re, Complex.div_im,
      Complex.add_re, Complex.ofReal_re, Complex.mul_im, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, zero_add, add_zero, sub_zero,
      Complex.normSq_apply, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Real.sin_neg, Real.cos_neg, abs_of_nonneg hdiff]
    rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub, Real.sin_add]
    field_simp [hβ.ne', hk.ne', hep.ne', hπ]
    ring
  · have hdiff : r-r' ≤ 0 := sub_nonpos.mpr (le_of_not_ge hr)
    unfold bulkCutLayer bulkBoundaryDensity normalMode
    simp only [Complex.add_im, Complex.sub_im, Complex.sub_re, Complex.div_im,
      Complex.add_re, Complex.ofReal_re, Complex.mul_im, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, zero_add, add_zero, sub_zero,
      Complex.normSq_apply, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Real.sin_neg, Real.cos_neg, abs_of_nonpos hdiff, neg_sub]
    rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub, Real.sin_add]
    field_simp [hβ.ne', hk.ne', hep.ne', hπ]
    ring

theorem bulkContinuum_positive {ι : Type*} [Fintype ι]
    {β k : ℝ} (hβ : 0 < β) (hk : 0 < k) (t : ℝ) (r v : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, v i *
      (bulkBoundaryDensity β k t * normalMode β k t (r i) * normalMode β k t (r j)) * v j := by
  calc
    _ = bulkBoundaryDensity β k t * (∑ i, v i * normalMode β k t (r i))^2 := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≥ 0 := by unfold bulkBoundaryDensity; positivity

theorem bulkAtom_positive {ι : Type*} [Fintype ι] {β b M₂ : ℝ}
    (hβ : 0 < β) (hb : b < M₂) (r v : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, v i *
      (bulkResidue β b M₂ * Real.exp (-(r i)*bulkKappa β b M₂) *
        Real.exp (-(r j)*bulkKappa β b M₂)) * v j := by
  calc
    _ = bulkResidue β b M₂ * (∑ i, v i * Real.exp (-(r i)*bulkKappa β b M₂))^2 := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≥ 0 := mul_nonneg (bulkResidue_positive hβ hb).le (sq_nonneg _)

private theorem cauchy_integrable (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun k : ℝ => (k^2+c^2)⁻¹) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun k : ℝ => (1+k^2)⁻¹) 0 (inv_pos.mpr hc)).mpr (by simpa using
    (integrable_inv_one_add_sq.integrableOn (s := Ioi 0)))
  have hh : IntegrableOn (fun x : ℝ => (c^2)⁻¹ * (1+(c⁻¹*x)^2)⁻¹) (Ioi 0) := h.const_mul _
  refine hh.congr_fun ?_ measurableSet_Ioi
  intro k _
  change (c^2)⁻¹ * (1+(c⁻¹*k)^2)⁻¹ = (k^2+c^2)⁻¹
  have hne : 1+(c⁻¹*k)^2 ≠ 0 := by positivity
  have hneq : k^2+c^2 ≠ 0 := by positivity
  field_simp
  ring

private theorem cauchy_integral (c : ℝ) (hc : 0 < c) :
    (∫ k : ℝ in Ioi 0, (k^2+c^2)⁻¹) = Real.pi/(2*c) := by
  have hne (k : ℝ) : k^2+c^2 ≠ 0 := by positivity
  calc
    _ = ∫ k : ℝ in Ioi 0, (c^2)⁻¹ * (1+(c⁻¹*k)^2)⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro k _
      have hnes : 1+(c⁻¹*k)^2 ≠ 0 := by positivity
      field_simp
      ring
    _ = _ := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi
        (fun k : ℝ => (1+k^2)⁻¹) 0 (inv_pos.mpr hc)]
      simp only [mul_zero, inv_inv, smul_eq_mul, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]
      field_simp

/-- Exact normalization of the boundary atom and continuum. The proof
uses a change to normal momentum and an elementary partial-fraction
integral, independent of any assumed spectral representation. -/
theorem bulkBoundary_mass {β b M₂ : ℝ} (hβ : 0 < β) (hb : b < M₂) :
    IntegrableOn (fun s => bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)) (Ioi M₂) ∧
    bulkResidue β b M₂ +
      (∫ s : ℝ in Ioi M₂, bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)) = 1 := by
  let u := bulkKappa β b M₂
  let v := u+β
  have hu : 0 < u := bulkKappa_pos hβ hb
  have hv : 0 < v := by dsimp [v]; positivity
  have huv : u < v := by dsimp [v]; linarith
  have heq : u*v = M₂-b := by
    dsimp [v, u]
    nlinarith [bulkKappa_sq_add (β := β) hb]
  have hsplit (k : ℝ) :
      (b-(k^2+M₂))^2+(β*k)^2 = (k^2+u^2)*(k^2+v^2) := by
    have h₁ : b - (k^2+M₂) = -(k^2+u*v) := by linarith
    rw [h₁]
    dsimp [v]
    ring
  let f := fun s => bulkBoundaryDensity β (Real.sqrt (s-M₂)) (b-s)
  let g := fun k : ℝ => |2*k| • f (k^2+M₂)
  let g0 := fun k : ℝ => (2*β/(Real.pi*(v^2-u^2))) *
    (v^2*(k^2+v^2)⁻¹ - u^2*(k^2+u^2)⁻¹)
  have hsq : 0 < v^2-u^2 := sub_pos.mpr ((sq_lt_sq₀ hu.le hv.le).mpr huv)
  have hg : EqOn g g0 (Ioi 0) := by
    intro k hk
    change 0 < k at hk
    have ht : k^2+M₂-M₂ = k^2 := by ring
    have hu' : 0 < k^2+u^2 := by positivity
    have hv' : 0 < k^2+v^2 := by positivity
    dsimp only [g, g0, f, bulkBoundaryDensity, smul_eq_mul]
    rw [ht, Real.sqrt_sq hk.le, abs_of_pos (by positivity : 0 < 2*k), hsplit]
    field_simp [Real.pi_ne_zero, hsq.ne', hu'.ne', hv'.ne']
    ring
  have hiu := (cauchy_integrable u hu).const_mul (u^2)
  have hiv := (cauchy_integrable v hv).const_mul (v^2)
  have hg0 : IntegrableOn g0 (Ioi 0) := (hiv.sub hiu).const_mul _
  have hgi : IntegrableOn g (Ioi 0) :=
    hg0.congr_fun (fun k hk => (hg hk).symm) measurableSet_Ioi
  have hgint : (∫ k : ℝ in Ioi 0, g k) = β/(u+v) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hg]
    change (∫ k : ℝ in Ioi 0, (2*β/(Real.pi*(v^2-u^2))) *
      (v^2*(k^2+v^2)⁻¹ - u^2*(k^2+u^2)⁻¹)) = _
    rw [integral_const_mul, integral_sub hiv hiu, integral_const_mul, integral_const_mul,
      cauchy_integral v hv, cauchy_integral u hu]
    have huv' : 0 < u+v := by positivity
    field_simp [Real.pi_ne_zero, hu.ne', hv.ne', (sub_ne_zero.mpr huv.ne'), hsq.ne', huv'.ne']
    ring
  have hder : ∀ k ∈ Ioi (0:ℝ), HasDerivWithinAt (fun k : ℝ => k^2+M₂) (2*k) (Ioi 0) k := by
    intro k _
    exact (by simpa using (((hasDerivAt_id k).pow 2).add_const M₂).hasDerivWithinAt)
  have hinj : InjOn (fun k : ℝ => k^2+M₂) (Ioi 0) := by
    apply StrictMonoOn.injOn
    intro r hr k hk h
    exact add_lt_add_right ((sq_lt_sq₀ hr.le hk.le).mpr h) M₂
  have himage : (fun k : ℝ => k^2+M₂) '' Ioi 0 = Ioi M₂ := by
    ext s
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (show M₂ < k^2 + M₂ by linarith [sq_pos_of_pos (mem_Ioi.mp hk)])
    · intro hs
      have h : 0 < s-M₂ := sub_pos.mpr hs
      exact ⟨Real.sqrt (s-M₂), Real.sqrt_pos.mpr h, by change Real.sqrt (s-M₂)^2+M₂=s; rw [Real.sq_sqrt h.le]; ring⟩
  have hcomp := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj f
  have hInt := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hder hinj f
  rw [himage] at hcomp hInt
  refine ⟨hInt.mpr hgi, ?_⟩
  rw [hcomp, hgint]
  change (1+β/(2*u))⁻¹ + β/(u+v) = 1
  have hden : 0 < 1+β/(2*u) := by positivity
  have hsum : 0 < u+v := by positivity
  field_simp [hu.ne', hden.ne', hsum.ne']
  dsimp [v]
  ring

end UV.RevisionSpectrum
