import UV.ContinueCollarEigenSpectrum
import UV.ContinueCollarHSIdentity

/-! The determinant-weighted traces of normalized Dirichlet eigenmodes.
A preparation by an arbitrary positive trace-class density is evaluated
through its square root, independently of the radial eigenbasis. -/

noncomputable section

open Real Set Filter MeasureTheory
open scoped Topology

namespace UV.CollarEigenmode

theorem weighted_eigenfamily_trace {j A α : ℝ} (hj : j ≠ 0) (hA : 0 < A) (hα : 0 < α)
    (E : ℕ → ℝ) (hE : ∀ n : ℕ,α*(n:ℝ)^2 ≤ E n) (u g : ℕ → ℝ → ℝ)
    (hc : ∀ n,ContinuousOn (u n) (Icc 0 1)) (hz : ∀ n,u n 0=0)
    (hu : ∀ n x,x ∈ Ioo 0 1 → HasDerivAt (u n) (g n x) x)
    (hg : ∀ n x,x ∈ Ioo 0 1 → HasDerivAt (g n) ((potential j x-E n)*u n x) x)
    (hn : ∀ n,(∫ r in Ioc (0:ℝ) 1,u n r^2)=1) (F : ℝ → ℝ) (hm : Measurable F) (hF : ∀ r,0 ≤ F r)
    (hFb : ∀ r ∈ Ioc (0:ℝ) 1,F r ≤ exp (logWeight A r)) :
    let W := fun n => ∫ r in Ioc (0:ℝ) 1,F r*u n r^2
    (∀ n,IntegrableOn (fun r => F r*u n r^2) (Ioc 0 1)) ∧
      ∃ C : ℝ,0 ≤ C ∧ ∀ t : ℝ,0 < t → t ≤ 1 →
        Summable (fun n => W n*exp (-2*t*E n)) ∧
        (0 < ∑' n,W n*exp (-2*t*E n) → log (∑' n,W n*exp (-2*t*E n)) ≤ C*ResumeCollarSpectral.collarScale t) := by
  obtain ⟨B,hB,h⟩ := weighted_mode_spectral_bound hj hA
  have h' (n) := h (E n) ((mul_nonneg hα.le (sq_nonneg (n:ℝ))).trans (hE n))
    (u n) (g n) (hc n) (hz n) (hu n) (hg n) (hn n) F hm hF hFb
  exact ⟨fun n => (h' n).1,ResumeCollarSpectral.collar_spectral_trace_upper hB hα E _ hE
    (fun _ => integral_nonneg fun r => mul_nonneg (hF r) (sq_nonneg _)) (fun n => (h' n).2)⟩

/-- For D = S S*, the trace of the positive prepared density
A D A* equals the squared Hilbert–Schmidt sum of A S. Its strict
positivity needs only injectivity of the collar A and S ≠ 0. -/
theorem positive_preparation {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (S A : H →L[ℂ] H) (hS : S ≠ 0) (hA : Function.Injective A) (hs : Summable (fun i => ‖S (b i)‖^2)) :
    Summable (fun i => ‖A (S (b i))‖^2) ∧ 0 < ∑' i, ‖A (S (b i))‖^2 ∧
      (∑' i, ‖A (S (b i))‖^2) ≤ ‖A‖^2*(∑' i, ‖S (b i)‖^2) := by
  have hle (i) : ‖A (S (b i))‖^2 ≤ ‖A‖^2*‖S (b i)‖^2 := by
    rw [←mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
  have hsm := hs.mul_left (‖A‖^2)
  have hh := Summable.of_nonneg_of_le (fun i => sq_nonneg ‖A (S (b i))‖) hle hsm
  have hnon : ∃ i,S (b i) ≠ 0 := by
    by_contra! hz
    apply hS
    ext x
    have h := (b.hasSum_repr x).mapL S
    have hs : HasSum (fun _ : ι => (0:H)) (S x) := by simpa only [map_smul,hz,smul_zero] using h
    exact hs.unique hasSum_zero
  obtain ⟨i,hi⟩ := hnon
  have hn : A (S (b i)) ≠ 0 := fun h => hi (hA (h.trans A.map_zero.symm))
  have hp := sq_pos_of_pos (norm_pos_iff.mpr hn)
  refine ⟨hh,hp.trans_le (hh.le_tsum i (fun k _ => sq_nonneg _)),?_⟩
  rw [←hs.tsum_mul_left]
  exact hh.tsum_le_tsum hle hsm

end UV.CollarEigenmode
