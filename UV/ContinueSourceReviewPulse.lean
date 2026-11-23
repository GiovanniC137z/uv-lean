import UV.ContinueSourceReviewReference
import Mathlib.LinearAlgebra.Matrix.Spectrum

/-! The normalized finite-dimensional sea functional for arbitrary source
profiles via the integral evolution equation, and the exact converse from
a single constant Hermitian pulse via spectral calculus. -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix ComplexConjugate

namespace UV

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

private def seaSpectralMatrix (U : Matrix κ κ ℂ) (f : κ → ℝ) : Matrix κ κ ℂ :=
  U * Matrix.diagonal (fun j => (f j : ℂ)) * Uᴴ

private theorem sea_spectral_expectation (U : Matrix κ κ ℂ) (f : κ → ℝ) (A : κ) :
    (seaSpectralMatrix U f A A).re = ∑ i, Complex.normSq (U A i)*f i := by
  rw [seaSpectralMatrix,Matrix.mul_apply,Complex.re_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Matrix.mul_diagonal,Matrix.conjTranspose_apply]
  change ((U A i*(f i : ℂ))*conj (U A i)).re = _
  rw [mul_right_comm,Complex.mul_conj,←Complex.ofReal_mul,Complex.ofReal_re]

def seaConstantPulse {K : Matrix κ κ ℂ} (hK : K.IsHermitian) (T : ℝ) : Matrix κ κ ℂ :=
  seaSpectralMatrix hK.eigenvectorUnitary (fun i => Real.exp (-T*hK.eigenvalues i))

private theorem sea_zero_column_of_pulse {K : Matrix κ κ ℂ} (hK : K.IsHermitian) (A : κ) {T : ℝ} (hT : 0 < T)
    (hmean : K A A = 0) (hpulse : (seaConstantPulse hK T A A).re = 1) : ∀ X, K X A = 0 := by
  let U : Matrix κ κ ℂ := hK.eigenvectorUnitary
  let w := fun j => Complex.normSq (U A j)
  let e := hK.eigenvalues
  have hspec : K = seaSpectralMatrix U e := hK.spectral_theorem
  have hmass : ∑ j, w j = 1 := by
    have hu : U*Uᴴ = 1 := (Matrix.mem_unitaryGroup_iff.mp hK.eigenvectorUnitary.2)
    have he : seaSpectralMatrix U (fun _ => 1) = 1 := by simpa [seaSpectralMatrix] using hu
    have h := sea_spectral_expectation U (fun _ => 1) A
    rw [he] at h
    simpa [w] using h.symm
  have hfirst : ∑ j, w j * e j = 0 := by
    have h := sea_spectral_expectation U e A
    rw [←hspec,hmean,Complex.zero_re] at h
    exact h.symm
  have hheat : ∑ j, w j * Real.exp (-T*e j) = 1 :=
    (sea_spectral_expectation U _ A).symm.trans hpulse
  let g := fun j => w j*(Real.exp (-T*e j) - 1 + T*e j)
  have hpos (j) : 0 ≤ g j := mul_nonneg (Complex.normSq_nonneg _) (by linarith [Real.add_one_le_exp (-T*e j)])
  have hgsum : ∑ j, g j = 0 := by
    have he (j) : g j = (w j * Real.exp (-T*e j) - w j) + T*(w j*e j) := by dsimp [g]; ring
    simp_rw [he]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,hheat,hmass,hfirst]; ring
  have hzero (j) : U A j = 0 ∨ e j = 0 := by
    by_cases hj : e j = 0
    · exact Or.inr hj
    · left
      have hp : 0 < Real.exp (-T*e j)-1+T*e j := by
        linarith [Real.add_one_lt_exp (mul_ne_zero (neg_ne_zero.mpr hT.ne') hj)]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hpos j)).mp hgsum j (Finset.mem_univ j)
      exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hp.ne')
  intro X
  rw [hspec,seaSpectralMatrix,Matrix.mul_apply]
  apply Finset.sum_eq_zero; intro j _
  rw [Matrix.mul_diagonal,Matrix.conjTranspose_apply]
  rcases hzero j with h | h <;> simp [h]

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def seaFreeGenerator (A : Finset ι) (ε : ι → ℝ) : Matrix (Finset ι) (Finset ι) ℂ :=
  Matrix.diagonal (fun X => (((∑ i ∈ X, ε i)-(∑ i ∈ A, ε i) : ℝ) : ℂ))

omit [Fintype ι] in
theorem sea_free_generator_hermitian (A : Finset ι) (ε : ι → ℝ) :
    (seaFreeGenerator A ε).IsHermitian := by
  rw [seaFreeGenerator,Matrix.isHermitian_diagonal_iff]
  intro X
  simp [IsSelfAdjoint]

omit [Fintype ι] in
private theorem sea_generator_vacuum (A : Finset ι) (ε : ι → ℝ) (X : Finset ι) : seaFreeGenerator A ε X A = 0 := by
  by_cases h : X = A <;> simp [seaFreeGenerator,h]

theorem sea_constant_pulse_necessity (A : Finset ι) (ε : ι → ℝ) {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) {T : ℝ}
    (hT : 0 < T)
    (h : (seaConstantPulse ((sea_free_generator_hermitian A ε).add (sea_current_hermitian A hQ)) T A A).re = 1) :
    (1-seaProjection A)*Q*seaProjection A = 0 := by
  apply (sea_current_annihilates_iff A Q).mp
  have hk := (sea_free_generator_hermitian A ε).add (sea_current_hermitian A hQ)
  have hmean : (seaFreeGenerator A ε + seaCurrent A Q) A A = 0 := by
    rw [Matrix.add_apply,sea_generator_vacuum,sea_current_vacuum_expectation,add_zero]
  intro X
  simpa only [Matrix.add_apply,sea_generator_vacuum,zero_add] using sea_zero_column_of_pulse hk A hT hmean h X

/-- The Fock-space integral equation for arbitrary time profiles,
allowing in particular integrable profiles and piecewise-constant ones. -/
def SeaIntegralEvolution (A : Finset ι) (ε : ι → ℝ) (Q : ℝ → Matrix ι ι ℂ) (ψ : ℝ → Finset ι → ℂ)
    (T : ℝ) : Prop := ∀ (t : ℝ), t ∈ Set.Icc 0 T → ∀ X,
      ψ t X = (if X = A then 1 else 0) -
        ∫ s in (0:ℝ)..t, ((seaFreeGenerator A ε + seaCurrent A (Q s)) *ᵥ ψ s) X

theorem sea_source_functional_one (A : Finset ι) (ε : ι → ℝ) (Q : ℝ → Matrix ι ι ℂ) {ψ : ℝ → Finset ι → ℂ}
    {T : ℝ} (hT : 0 ≤ T) (hψ : SeaIntegralEvolution A ε Q ψ T)
    (hs : ∀ t ∈ Set.Icc 0 T, (Q t).IsHermitian)
    (hc : ∀ t ∈ Set.Icc 0 T, seaProjection A*Q t = Q t*seaProjection A) : ψ T A = 1 := by
  rw [hψ T ⟨hT,le_rfl⟩ A,if_pos rfl,intervalIntegral.integral_of_le hT]
  suffices hz : (∫ s in Set.Ioc 0 T, ((seaFreeGenerator A ε+seaCurrent A (Q s))*ᵥψ s) A) = 0 by simp [hz]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  have ht' : t ∈ Set.Icc 0 T := ⟨ht.1.le,ht.2⟩
  have hQ := hs t ht'
  have hcol := (sea_current_annihilates_iff A _).2 ((sea_commutes_iff_block A hQ).1 (hc t ht'))
  change ∑ X, _ = 0
  apply Finset.sum_eq_zero
  intro X _
  have hj := (sea_current_hermitian A hQ).apply A X
  have hk := (sea_free_generator_hermitian A ε).apply A X
  simp only [hcol,sea_generator_vacuum,star_zero] at hj hk
  simp only [Matrix.add_apply,←hj,←hk,add_zero,zero_mul]

private theorem sea_spectral_action {K : Matrix κ κ ℂ} (hK : K.IsHermitian) (f : κ → ℝ) :
    let U : Matrix κ κ ℂ := hK.eigenvectorUnitary
    K * seaSpectralMatrix U f = seaSpectralMatrix U (fun j => hK.eigenvalues j*f j) := by
  let U : Matrix κ κ ℂ := hK.eigenvectorUnitary
  let E : Matrix κ κ ℂ := Matrix.diagonal (fun i => (hK.eigenvalues i : ℂ))
  let F : Matrix κ κ ℂ := Matrix.diagonal (fun i => (f i : ℂ))
  have hspec : K = U*E*Uᴴ := hK.spectral_theorem
  have hU : Uᴴ*U=1 := Matrix.mem_unitaryGroup_iff'.mp hK.eigenvectorUnitary.2
  change K*(U*F*Uᴴ) = _
  calc K*(U*F*Uᴴ) = U*E*(Uᴴ*U)*F*Uᴴ := by rw [hspec]; noncomm_ring
       _ = U*(E*F)*Uᴴ := by rw [hU,mul_one,mul_assoc U E F]
       _ = _ := by simp only [seaSpectralMatrix,E,F,Matrix.diagonal_mul_diagonal,Complex.ofReal_mul,U]

private theorem sea_pulse_deriv {K : Matrix κ κ ℂ} (hK : K.IsHermitian) (X A : κ) (t : ℝ) :
    HasDerivAt (fun s => seaConstantPulse hK s X A) (-(K*seaConstantPulse hK t) X A) t := by
  let U : Matrix κ κ ℂ := hK.eigenvectorUnitary
  let e := hK.eigenvalues
  have hd (j : κ) : HasDerivAt (fun s : ℝ => (U X j*(Real.exp (-s*e j) : ℂ))*conj (U A j))
      (-((U X j*((e j*Real.exp (-t*e j):ℝ):ℂ))*conj (U A j))) t := by
    have h := (((hasDerivAt_id t).neg.mul_const (e j)).exp).ofReal_comp
    convert (h.const_mul (U X j)).mul_const (conj (U A j)) using 1
    simp; ring_nf; simp
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j)
  have heq (f : κ → ℝ) : seaSpectralMatrix U f X A = ∑ j, (U X j*(f j : ℂ))*conj (U A j) := by
    rw [seaSpectralMatrix,Matrix.mul_apply]; simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply]; rfl
  change HasDerivAt (fun s => seaSpectralMatrix U (fun j => Real.exp (-s*e j)) X A) (-(K*seaSpectralMatrix U (fun j => Real.exp (-t*e j))) X A) t
  rw [sea_spectral_action hK]
  change HasDerivAt (fun s => seaSpectralMatrix U (fun j => Real.exp (-s*e j)) X A) (-(seaSpectralMatrix U (fun j => e j*Real.exp (-t*e j)) X A)) t
  simp_rw [heq]
  simpa only [Finset.sum_neg_distrib] using h

theorem sea_constant_pulse_evolves (A : Finset ι) (ε : ι → ℝ) {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) (T : ℝ) :
    let hK := (sea_free_generator_hermitian A ε).add (sea_current_hermitian A hQ)
    SeaIntegralEvolution A ε (fun _ => Q) (fun t X => seaConstantPulse hK t X A) T := by
  let K := seaFreeGenerator A ε + seaCurrent A Q
  let hK : K.IsHermitian := (sea_free_generator_hermitian A ε).add (sea_current_hermitian A hQ)
  let U : Matrix (Finset ι) (Finset ι) ℂ := hK.eigenvectorUnitary
  have hinit : seaConstantPulse hK 0 = 1 := by
    have hu : U*Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hK.eigenvectorUnitary.2
    simpa [seaConstantPulse,seaSpectralMatrix,U] using hu
  dsimp only
  intro t _ X
  have hc (Y) : Continuous (fun s => seaConstantPulse hK s Y A) :=
    continuous_iff_continuousAt.mpr fun s => (sea_pulse_deriv hK Y A s).continuousAt
  have hf : Continuous (fun s => -(K*seaConstantPulse hK s) X A) := by
    simp only [Matrix.mul_apply]
    exact (continuous_finset_sum _ (fun Y _ => continuous_const.mul (hc Y))).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (fun s _ => sea_pulse_deriv hK X A s) (hf.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg,hinit,Matrix.one_apply] at h
  change seaConstantPulse hK t X A = (if X = A then 1 else 0) - ∫ s in (0:ℝ)..t, (K*seaConstantPulse hK s) X A
  linear_combination -h

/-- Equivalence for the finite occupied orbital space. Sufficiency covers
arbitrary source profiles satisfying the integral evolution equation.
Necessity already follows from constant sources on a slab of length one. -/
theorem sea_finite_reference_test (A : Finset ι) (ε : ι → ℝ) (S : Set (Matrix ι ι ℂ))
    (hS : ∀ q ∈ S, q.IsHermitian) :
    (∀ (T : ℝ), 0 < T → ∀ (Q : ℝ → Matrix ι ι ℂ), (∀ s ∈ Set.Icc 0 T, Q s ∈ S) →
      ∀ (ψ : ℝ → Finset ι → ℂ), SeaIntegralEvolution A ε Q ψ T → ψ T A = 1) ↔
      ∀ q ∈ S, seaProjection A*q = q*seaProjection A := by
  constructor
  · intro h q hq
    have he := sea_constant_pulse_evolves A ε (hS q hq) 1
    have hv := h 1 zero_lt_one (fun _ => q) (fun _ _ => hq) _ he
    exact (sea_commutes_iff_block A (hS q hq)).2 (sea_constant_pulse_necessity A ε (hS q hq) zero_lt_one (by rw [hv,Complex.one_re]))
  · intro h T hT Q hQ ψ hψ
    exact sea_source_functional_one A ε Q hT.le hψ (fun t ht => hS _ (hQ t ht)) (fun t ht => h _ (hQ t ht))

end UV
