import UV.RevisionSpectrumSewing
import Mathlib.Algebra.Group.ForwardDiff

/-! A finite difference cancels the contact polynomial and each polynomial
dispersion subtraction before the positive spectral estimate is taken. -/

noncomputable section
open MeasureTheory Filter Set Polynomial
open scoped ENNReal Topology fwdDiff

namespace UV.ContinuationSewing

open UV.RevisionSpectrum (reciprocalDiff)

private theorem reciprocalDiff_scaled (h x : ℝ) (f : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    reciprocalDiff h n f (x+h*t) = (-1:ℝ)^n * (Δ_[1]^[n] fun u : ℝ => f (x+h*u)) t := by
  induction n generalizing t with
  | zero => simp [reciprocalDiff]
  | succ n ih =>
    rw [Function.iterate_succ_apply', fwdDiff, pow_succ]
    change reciprocalDiff h n f (x+h*t) - reciprocalDiff h n f (x+h*t+h) =
      (-1:ℝ)^n*(-1) * ((Δ_[1]^[n] fun u : ℝ => f (x+h*u)) (t+1) -
        (Δ_[1]^[n] fun u : ℝ => f (x+h*u)) t)
    rw [show x+h*t+h = x+h*(t+1) by ring, ih, ih]
    ring

theorem reciprocalDiff_polynomial (P : Polynomial ℝ) (h x : ℝ) {n : ℕ}
    (hP : P.natDegree < n) : reciprocalDiff h n P.eval x = 0 := by
  let L : Polynomial ℝ := C x + C h * Polynomial.X
  let Q := P.comp L
  have hL : L.natDegree ≤ 1 := by
    unfold L
    apply (Polynomial.natDegree_add_le _ _).trans
    rw [Polynomial.natDegree_C]
    have hh := Polynomial.natDegree_mul_le (p := C h) (q := (Polynomial.X : Polynomial ℝ))
    simpa using hh
  have hQ : Q.natDegree < n :=
    ((Polynomial.natDegree_comp_le (p := P) (q := L)).trans
      (by calc
        _ ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ hL
        _ = _ := Nat.mul_one _)).trans_lt hP
  have heq : (fun u : ℝ => P.eval (x+h*u)) = Q.eval := by
    funext u
    simp [Q, L, Polynomial.eval_comp]
  have hr := reciprocalDiff_scaled h x P.eval n 0
  rw [heq, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hQ] at hr
  simpa using hr

theorem reciprocalDiff_add (h : ℝ) (n : ℕ) (f g : ℝ → ℝ) (x : ℝ) :
    reciprocalDiff h n (fun y => f y+g y) x =
      reciprocalDiff h n f x + reciprocalDiff h n g x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change reciprocalDiff h n (fun y => f y+g y) x -
      reciprocalDiff h n (fun y => f y+g y) (x+h) =
      (reciprocalDiff h n f x - reciprocalDiff h n f (x+h)) +
      (reciprocalDiff h n g x - reciprocalDiff h n g (x+h))
    rw [ih, ih]
    ring

theorem reciprocalDiff_mul (h c : ℝ) (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    reciprocalDiff h n (fun y => c*f y) x = c*reciprocalDiff h n f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change reciprocalDiff h n (fun y => c*f y) x -
      reciprocalDiff h n (fun y => c*f y) (x+h) =
      c * (reciprocalDiff h n f x - reciprocalDiff h n f (x+h))
    rw [ih, ih]
    ring

private theorem reciprocalDiff_congr_above {f g : ℝ → ℝ} {h R : ℝ}
    (hh : 0 ≤ h) (heq : ∀ z ≥ R, f z = g z) (n : ℕ) (x : ℝ) (hx : R ≤ x) :
    reciprocalDiff h n f x = reciprocalDiff h n g x := by
  induction n generalizing x with
  | zero => exact heq x hx
  | succ n ih =>
    change (reciprocalDiff h n f x - reciprocalDiff h n f (x+h)) =
      (reciprocalDiff h n g x - reciprocalDiff h n g (x+h))
    rw [ih x hx, ih (x+h) (by linarith)]

theorem reciprocalDiff_integral (ρ : Measure ℝ) (f : ℝ → ℝ → ℝ)
    {h R : ℝ} (hh : 0 ≤ h) (hf : ∀ x ≥ R, Integrable (f x) ρ)
    (n : ℕ) (x : ℝ) (hx : R ≤ x) :
    Integrable (fun s => reciprocalDiff h n (fun y => f y s) x) ρ ∧
      reciprocalDiff h n (fun y => ∫ s, f y s ∂ρ) x =
        ∫ s, reciprocalDiff h n (fun y => f y s) x ∂ρ := by
  induction n generalizing x with
  | zero => exact ⟨hf x hx, rfl⟩
  | succ n ih =>
    obtain ⟨ha, hea⟩ := ih x hx
    obtain ⟨hb, heb⟩ := ih (x+h) (by linarith)
    constructor
    · exact ha.sub hb
    · change reciprocalDiff h n (fun y => ∫ s, f y s ∂ρ) x -
        reciprocalDiff h n (fun y => ∫ s, f y s ∂ρ) (x+h) =
        ∫ s, reciprocalDiff h n (fun y => f y s) x -
          reciprocalDiff h n (fun y => f y s) (x+h) ∂ρ
      rw [hea, heb, integral_sub ha hb]

/-- The positive kernel surviving the subtraction and fixed-step differencing. -/
def differenceKernel (n : ℕ) (s x h : ℝ) : ℝ :=
  ((n+1).factorial*s*h^(n+1)) / ∏ j ∈ Finset.range (n+1+1), (s+x+(j:ℝ)*h)

theorem reciprocalDiff_transverse_signed (s x h : ℝ) (hs : 0 ≤ s) (hx : 0 < x)
    (hh : 0 ≤ h) (n : ℕ) :
    reciprocalDiff h (n+1) (fun y => y/(s+y)) x = -differenceKernel n s x h := by
  have heq (y : ℝ) (hy : y ≥ x) : y/(s+y) = 1+(-s)*(s+y)⁻¹ := by
    have hy' : 0 < y := hx.trans_le hy
    have hsy : 0 < s+y := by positivity
    field_simp [hsy.ne']
    ring
  rw [reciprocalDiff_congr_above hh heq (n+1) x le_rfl]
  rw [reciprocalDiff_add, reciprocalDiff_mul]
  have hz := reciprocalDiff_polynomial (C (1:ℝ)) h x (n := n+1) (by simp)
  simp only [Polynomial.eval_C] at hz
  rw [hz, zero_add, UV.RevisionSpectrum.reciprocalDiff_inv s x h (by positivity) hh]
  unfold differenceKernel
  ring

/-- The polynomial g s is the spectral subtraction at mass s. The
integrability hypothesis concerns only the complete subtracted kernel. -/
theorem difference_subtracted_integral (ρ : Measure ℝ) (g : ℝ → Polynomial ℝ)
    {h R : ℝ} (hR : 0 < R) (hh : 0 ≤ h) (n : ℕ)
    (hs : ∀ᵐ s ∂ρ, 0 ≤ s) (hg : ∀ᵐ s ∂ρ, (g s).natDegree < n+1)
    (hf : ∀ x ≥ R, Integrable (fun s => x/(s+x) - (g s).eval x) ρ)
    (x : ℝ) (hx : R ≤ x) :
    Integrable (fun s => differenceKernel n s x h) ρ ∧
      reciprocalDiff h (n+1) (fun y => ∫ s, y/(s+y) - (g s).eval y ∂ρ) x =
        -(∫ s, differenceKernel n s x h ∂ρ) := by
  obtain ⟨hi, heq⟩ := reciprocalDiff_integral ρ
    (fun y s => y/(s+y) - (g s).eval y) hh hf (n+1) x hx
  have hcomp : (fun s => reciprocalDiff h (n+1) (fun y => y/(s+y) - (g s).eval y) x) =ᵐ[ρ]
      (fun s => -differenceKernel n s x h) := by
    filter_upwards [hs, hg] with s hsp hgp
    have hmul : (fun y => y/(s+y) - (g s).eval y) =
        (fun y => y/(s+y) + (-1) * (g s).eval y) := by funext y; ring
    rw [hmul, reciprocalDiff_add, reciprocalDiff_mul,
      reciprocalDiff_polynomial (g s) h x hgp, mul_zero, add_zero]
    exact reciprocalDiff_transverse_signed s x h hsp (hR.trans_le hx) hh n
  constructor
  · exact (hi.congr hcomp).neg.congr (Eventually.of_forall fun s => neg_neg _)
  · rw [heq, integral_congr_ae hcomp, integral_neg]

end UV.ContinuationSewing
