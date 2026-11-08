import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The exact operator-norm obstruction uses only the Hermitian involution
given by the Euclidean Clifford contraction with a real unit vector. -/

noncomputable section
open scoped ComplexConjugate

namespace UV

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A]
    [StarModule ℂ A] [CStarRing A] [NormOneClass A]

def wardRadialSymbol (G : A) (r c : ℝ) : A :=
  (Complex.I * (r : ℂ)) • G + (c : ℂ) • (1 : A)

omit [CStarRing A] [NormOneClass A] in
/-- The Hermitian unit involution is derived from the actual Clifford
anticommutators and a real Euclidean unit vector. -/
theorem clifford_unit_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → A) (hγ : ∀ i, star (γ i) = γ i)
    (hClifford : ∀ i j, γ i * γ j + γ j * γ i =
      if i = j then (2 : ℂ) • (1 : A) else 0)
    (u : ι → ℝ) (hu : ∑ i, u i ^ 2 = 1) :
    let G := ∑ i, (u i : ℂ) • γ i
    star G = G ∧ G * G = 1 := by
  classical
  dsimp only
  let G := ∑ i, (u i : ℂ) • γ i
  have he : G * G = ∑ i, ∑ j, ((u i : ℂ) * (u j : ℂ)) • (γ i * γ j) := by
    dsimp only [G]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hs : (∑ i, ∑ j, ((u i : ℂ) * (u j : ℂ)) • (γ j * γ i)) = G * G := by
    rw [he, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (u j : ℂ)]
  have hp : (2 : ℂ) • (G * G) = (2 : ℂ) • (1 : A) := by
    calc
      _ = (∑ i, ∑ j, ((u i : ℂ) * (u j : ℂ)) • (γ i * γ j + γ j * γ i)) := by
        simp only [smul_add, Finset.sum_add_distrib, ← he, hs, two_smul]
      _ = ∑ i, ((2 : ℂ) * (u i : ℂ) ^ 2) • (1 : A) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [hClifford, smul_ite, smul_zero, smul_smul]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_univ, if_pos]
        congr 1
        ring
      _ = _ := by
        rw [← Finset.sum_smul]
        congr 1
        rw [← Finset.mul_sum]
        have hc : ∑ i, (u i : ℂ) ^ 2 = 1 := by exact_mod_cast hu
        rw [hc, mul_one]
  refine ⟨?_, (smul_right_injective A (by norm_num : (2 : ℂ) ≠ 0)) hp⟩
  simp only [star_sum, star_smul, hγ]
  congr 1
  ext i
  simp

omit [CStarRing A] [NormOneClass A] in
theorem wardRadialSymbol_star_mul (G : A) (hG : star G = G) (hG2 : G * G = 1)
    (r c : ℝ) :
    star (wardRadialSymbol G r c) * wardRadialSymbol G r c =
      ((r ^ 2 + c ^ 2 : ℝ) : ℂ) • (1 : A) := by
  unfold wardRadialSymbol
  simp only [star_add, star_smul, hG, star_one, map_mul, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, smul_add, smul_smul, hG2, one_mul, mul_one]
  have hI : (Complex.I * (r : ℂ)) * (-Complex.I * (r : ℂ)) = (r : ℂ) ^ 2 := by
    calc
      _ = -(Complex.I * Complex.I) * (r : ℂ) ^ 2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [hI]
  push_cast
  module

theorem wardRadialSymbol_norm_sq (G : A) (hG : star G = G) (hG2 : G * G = 1)
    (r c : ℝ) : ‖wardRadialSymbol G r c‖ ^ 2 = r ^ 2 + c ^ 2 := by
  have he := CStarRing.norm_star_mul_self (x := wardRadialSymbol G r c)
  rw [wardRadialSymbol_star_mul G hG hG2, norm_smul, norm_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at he
  nlinarith

theorem wardRadialSymbol_norm_lower (G : A) (hG : star G = G) (hG2 : G * G = 1)
    (r c : ℝ) : r ≤ ‖wardRadialSymbol G r c‖ := by
  have he := wardRadialSymbol_norm_sq G hG hG2 r c
  nlinarith [norm_nonneg (wardRadialSymbol G r c), sq_nonneg c]

omit [StarRing A] [StarModule ℂ A] [CStarRing A] [NormOneClass A] in
/-- The radial Ward identity is the source premise. Dividing by the actual
nonzero photon momentum derives the contracted vertex. -/
theorem radial_ward_forces_symbol {G V : A} {R AR A0 m : ℝ} (hR : 0 < R)
    (hWard : (R : ℂ) • V =
      (Complex.I * ((AR * R : ℝ) : ℂ)) • G + ((m * (AR - A0) : ℝ) : ℂ) • (1 : A)) :
    V = wardRadialSymbol G AR (m * (AR - A0) / R) := by
  have hh := congrArg (fun W : A => (R : ℂ)⁻¹ • W) hWard
  dsimp only at hh
  rw [inv_smul_smul₀ (by exact_mod_cast hR.ne')] at hh
  rw [hh]
  unfold wardRadialSymbol
  rw [smul_add, smul_smul, smul_smul]
  congr 1
  · congr 1
    push_cast
    field_simp [show (R : ℂ) ≠ 0 by exact_mod_cast hR.ne']
  · congr 1
    push_cast
    field_simp

theorem ward_vertex_exact_norm {G V : A} (hG : star G = G) (hG2 : G * G = 1)
    {R FR F0 m : ℝ} (hR : 0 < R)
    (hWard : (R : ℂ) • V =
      (Complex.I * ((FR⁻¹ * R : ℝ) : ℂ)) • G +
        ((m * (FR⁻¹ - F0⁻¹) : ℝ) : ℂ) • (1 : A)) :
    ‖V‖ ^ 2 = FR⁻¹ ^ 2 + m ^ 2 / R ^ 2 * (FR⁻¹ - F0⁻¹) ^ 2 ∧
      FR⁻¹ ≤ ‖V‖ := by
  have he := radial_ward_forces_symbol hR hWard
  rw [he]
  constructor
  · rw [wardRadialSymbol_norm_sq G hG hG2]
    field_simp
  · exact wardRadialSymbol_norm_lower G hG hG2 _ _

theorem wardRadialSymbol_scaled_dirac_norm (G : A) (hG : star G = G) (hG2 : G * G = 1)
    {R AR m : ℝ} (hR : 0 < R) (hAR : 0 ≤ AR) :
    ‖wardRadialSymbol G AR (m * AR / R)‖ = Real.sqrt (R ^ 2 + m ^ 2) * AR / R := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [wardRadialSymbol_norm_sq G hG hG2]
  have hs := Real.sq_sqrt (show 0 ≤ R ^ 2 + m ^ 2 by positivity)
  field_simp
  nlinarith

/-- The reverse-triangle lower bound stated in the source, in addition to
the exact norm-square certificate. -/
theorem ward_vertex_growth_lower {G V : A} (hG : star G = G) (hG2 : G * G = 1)
    {R FR F0 m : ℝ} (hR : 0 < R) (hFR : 0 < FR) (hF0 : 0 < F0) (hm : 0 ≤ m)
    (hWard : (R : ℂ) • V =
      (Complex.I * ((FR⁻¹ * R : ℝ) : ℂ)) • G +
        ((m * (FR⁻¹ - F0⁻¹) : ℝ) : ℂ) • (1 : A)) :
    (Real.sqrt (R ^ 2 + m ^ 2) / FR - m / F0) / R ≤ ‖V‖ := by
  have he := radial_ward_forces_symbol hR hWard
  have hsum : V + (((m * F0⁻¹ / R : ℝ) : ℂ) • (1 : A)) =
      wardRadialSymbol G FR⁻¹ (m * FR⁻¹ / R) := by
    rw [he]
    unfold wardRadialSymbol
    push_cast
    module
  have hn := norm_add_le V (((m * F0⁻¹ / R : ℝ) : ℂ) • (1 : A))
  rw [hsum, wardRadialSymbol_scaled_dirac_norm G hG hG2 hR (inv_nonneg.mpr hFR.le),
    norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)] at hn
  have hi : Real.sqrt (R ^ 2 + m ^ 2) * FR⁻¹ / R - m * F0⁻¹ / R =
      (Real.sqrt (R ^ 2 + m ^ 2) / FR - m / F0) / R := by ring
  rw [← hi]
  linarith

def cliffordSlash {ι : Type*} [Fintype ι] (γ : ι → A) (p : ι → ℝ) : A :=
  ∑ i, (p i : ℂ) • γ i

def cliffordInverseSymbol {ι : Type*} [Fintype ι]
    (γ : ι → A) (F : ℝ → ℝ) (m : ℝ) (p : ι → ℝ) : A :=
  (Complex.I * ((F (∑ i, p i ^ 2))⁻¹ : ℂ)) • cliffordSlash γ p +
    ((m * (F (∑ i, p i ^ 2))⁻¹ : ℝ) : ℂ) • (1 : A)

omit [StarRing A] [StarModule ℂ A] [CStarRing A] [NormOneClass A] in
theorem full_ward_radial_identity {ι : Type*} [Fintype ι]
    (γ : ι → A) (F : ℝ → ℝ) (m : ℝ)
    (Γ : ι → (ι → ℝ) → (ι → ℝ) → A)
    (hWTI : ∀ p' p, (∑ i, ((p' i - p i : ℝ) : ℂ) • Γ i p' p) =
      cliffordInverseSymbol γ F m p' - cliffordInverseSymbol γ F m p)
    (u : ι → ℝ) (hu : ∑ i, u i ^ 2 = 1) (R : ℝ) :
    (R : ℂ) • (∑ i, (u i : ℂ) • Γ i (fun j => R * u j) 0) =
      (Complex.I * (((F (R ^ 2))⁻¹ * R : ℝ) : ℂ)) • cliffordSlash γ u +
        ((m * ((F (R ^ 2))⁻¹ - (F 0)⁻¹) : ℝ) : ℂ) • (1 : A) := by
  have hp : ∑ i, (R * u i) ^ 2 = R ^ 2 := by
    simp only [mul_pow]
    rw [← Finset.mul_sum, hu, mul_one]
  have hs : cliffordSlash γ (fun i => R * u i) = (R : ℂ) • cliffordSlash γ u := by
    simp only [cliffordSlash, Finset.smul_sum, smul_smul, Complex.ofReal_mul]
  have he := hWTI (fun i => R * u i) 0
  simp only [Pi.zero_apply, sub_zero, Complex.ofReal_mul, ← smul_smul,
    ← Finset.smul_sum] at he
  rw [he]
  unfold cliffordInverseSymbol
  rw [hp, hs]
  simp only [Pi.zero_apply, zero_pow two_ne_zero, Finset.sum_const_zero,
    cliffordSlash, Complex.ofReal_zero, zero_smul, Finset.sum_const_zero, smul_zero, zero_add,
    smul_smul, Complex.ofReal_mul, Complex.ofReal_sub]
  module

/-- Full indexed Ward compatibility with the actual inverse symbol implies
the source norm certificates for its actual radial contraction. -/
theorem full_ward_vertex_norm_certificates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → A) (hγ : ∀ i, star (γ i) = γ i)
    (hClifford : ∀ i j, γ i * γ j + γ j * γ i =
      if i = j then (2 : ℂ) • (1 : A) else 0)
    (F : ℝ → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (Γ : ι → (ι → ℝ) → (ι → ℝ) → A)
    (hWTI : ∀ p' p, (∑ i, ((p' i - p i : ℝ) : ℂ) • Γ i p' p) =
      cliffordInverseSymbol γ F m p' - cliffordInverseSymbol γ F m p)
    (u : ι → ℝ) (hu : ∑ i, u i ^ 2 = 1) {R : ℝ} (hR : 0 < R)
    (hFR : 0 < F (R ^ 2)) (hF0 : 0 < F 0) :
    let V := ∑ i, (u i : ℂ) • Γ i (fun j => R * u j) 0
    ‖V‖ ^ 2 = (F (R ^ 2))⁻¹ ^ 2 + m ^ 2 / R ^ 2 * ((F (R ^ 2))⁻¹ - (F 0)⁻¹) ^ 2 ∧
      (F (R ^ 2))⁻¹ ≤ ‖V‖ ∧
      (Real.sqrt (R ^ 2 + m ^ 2) / F (R ^ 2) - m / F 0) / R ≤ ‖V‖ := by
  have hG := clifford_unit_contraction γ hγ hClifford u hu
  have hr := full_ward_radial_identity γ F m Γ hWTI u hu R
  have he := ward_vertex_exact_norm hG.1 hG.2 hR hr
  exact ⟨he.1, he.2, ward_vertex_growth_lower hG.1 hG.2 hR hFR hF0 hm hr⟩

omit [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A] [CStarRing A] [NormOneClass A] in
/-- A superpolynomially suppressed positive profile forces failure of every
global polynomial bound for the radial contracted vertex. -/
theorem superpolynomial_profile_forbids_polynomial_vertex
    (F : ℝ → ℝ) (V : ℝ → A)
    (hF : ∀ u, 0 ≤ u → 0 < F u)
    (hprofile : ∀ n : ℕ, Filter.Tendsto (fun R : ℝ => R ^ n * F (R ^ 2))
      Filter.atTop (nhds 0))
    (hvertex : ∀ R, 0 < R → (F (R ^ 2))⁻¹ ≤ ‖V R‖) :
    ¬ ∃ (C : ℝ) (D : ℕ), 0 ≤ C ∧ ∀ R, 1 ≤ R → ‖V R‖ ≤ C * (1 + R ^ D) := by
  rintro ⟨C, D, _, hC⟩
  have hzero : Filter.Tendsto (fun R : ℝ => F (R ^ 2)) Filter.atTop (nhds 0) := by
    simpa only [pow_zero, one_mul] using hprofile 0
  have hlim : Filter.Tendsto (fun R : ℝ => C * (F (R ^ 2) + R ^ D * F (R ^ 2)))
      Filter.atTop (nhds 0) := by
    simpa only [add_zero, mul_zero] using (hzero.add (hprofile D)).const_mul C
  have hb : ∀ᶠ R : ℝ in Filter.atTop, 1 ≤ C * (F (R ^ 2) + R ^ D * F (R ^ 2)) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
    have hp := hF (R ^ 2) (sq_nonneg R)
    have hlow := hvertex R (lt_of_lt_of_le zero_lt_one hR)
    have h1 : 1 ≤ F (R ^ 2) * ‖V R‖ := by
      have ht := mul_le_mul_of_nonneg_left hlow hp.le
      simpa only [mul_inv_cancel₀ hp.ne'] using ht
    have ht := mul_le_mul_of_nonneg_left (hC R hR) hp.le
    have heq : F (R ^ 2) * (C * (1 + R ^ D)) =
        C * (F (R ^ 2) + R ^ D * F (R ^ 2)) := by ring
    exact h1.trans (ht.trans_eq heq)
  have hc : ∀ᶠ R : ℝ in Filter.atTop,
      C * (F (R ^ 2) + R ^ D * F (R ^ 2)) < 1 :=
    (tendsto_order.mp hlim).2 1 zero_lt_one
  obtain ⟨R, hR, hR'⟩ := (hb.and hc).exists
  linarith

end UV
