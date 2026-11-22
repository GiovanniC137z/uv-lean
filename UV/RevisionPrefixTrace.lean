import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic

/-! The finite cyclic trace obstruction for orthogonal prefix records.
Subprojection is expressed as the usual absorption identities for projections. -/

namespace UV.RevisionPrefixTrace

open scoped BigOperators Matrix.Norms.Operator

section Trace

variable {A : Type*} [Ring A] [StarRing A]

/-- Positivity of a trace on squares implies that it is nonnegative on
the projection left over after finitely many orthogonal subprojections. -/
theorem trace_sum_subprojections {E : Type*} [Fintype E]
    (τ : A →+ ℝ) (positive : ∀ a, 0 ≤ τ (star a * a))
    (p : A) (q : E → A)
    (hp : p * p = p) (hps : star p = p)
    (hq : ∀ e, q e * q e = q e) (hqs : ∀ e, star (q e) = q e)
    (hleft : ∀ e, p * q e = q e) (hright : ∀ e, q e * p = q e)
    (horth : ∀ e f, e ≠ f → q e * q f = 0) :
    (∑ e, τ (q e)) ≤ τ p := by
  classical
  let Q := ∑ e, q e
  have hl : p * Q = Q := by simp [Q, Finset.mul_sum, hleft]
  have hr : Q * p = Q := by simp [Q, Finset.sum_mul, hright]
  have hs : star Q = Q := by simp [Q, hqs]
  have hQ : Q * Q = Q := by
    change (∑ e, q e) * Q = ∑ e, q e
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro e _
    change q e * (∑ f, q f) = q e
    rw [Finset.mul_sum, Finset.sum_eq_single e]
    · exact hq e
    · intro f _ hfe
      exact horth e f hfe.symm
    · simp
  have h := positive (p - Q)
  rw [star_sub, hps, hs, sub_mul, mul_sub, mul_sub, hp, hl, hr, hQ,
    sub_self, sub_zero, map_sub, map_sum] at h
  exact sub_nonneg.mp h

/-- A cyclic trace bounds the combined weight of every outgoing record family. -/
theorem prefix_trace_weights {V : Type*} (E : V → Type*) [∀ v, Fintype (E v)]
    (target : ∀ v, E v → V) (p : V → A) (S : ∀ v, E v → A) (τ : A →+ ℝ)
    (positive : ∀ a, 0 ≤ τ (star a * a))
    (cyclic : ∀ a b, τ (a * b) = τ (b * a))
    (hp : ∀ v, p v * p v = p v) (hps : ∀ v, star (p v) = p v)
    (hinitial : ∀ v e, star (S v e) * S v e = p (target v e))
    (hleft : ∀ v e, p v * (S v e * star (S v e)) = S v e * star (S v e))
    (hidempotent : ∀ v e, (S v e * star (S v e)) * (S v e * star (S v e)) =
        S v e * star (S v e))
    (horth : ∀ v (e f : E v), e ≠ f →
        (S v e * star (S v e)) * (S v f * star (S v f)) = 0) :
    ∀ v, (∑ e, τ (p (target v e))) ≤ τ (p v) := by
  intro v
  have hr (e : E v) := congrArg star (hleft v e)
  simp only [star_mul, star_star, hps] at hr
  have h := trace_sum_subprojections τ positive (p v) (fun e => S v e * star (S v e))
    (hp v) (hps v) (hidempotent v) (by simp) (hleft v) hr (horth v)
  simpa only [cyclic _ (star _), hinitial] using h

/-- One vertex with two loop records cannot have a normalized positive trace.
Faithfulness is unnecessary in this case. -/
theorem no_normalized_trace_two_loops (S : Fin 2 → A) (τ : A →+ ℝ)
    (positive : ∀ a, 0 ≤ τ (star a * a))
    (cyclic : ∀ a b, τ (a * b) = τ (b * a))
    (normalized : τ 1 = 1) (hinitial : ∀ e, star (S e) * S e = 1)
    (horth : ∀ e f, e ≠ f → (S e * star (S e)) * (S f * star (S f)) = 0) :
    False := by
  have h := trace_sum_subprojections τ positive (1 : A) (fun e => S e * star (S e))
    (by simp) (by simp)
    (by intro e; simp [mul_assoc, ← mul_assoc (star (S e)), hinitial])
    (by simp) (by simp) (by simp) horth
  have he (e : Fin 2) : τ (S e * star (S e)) = 1 :=
    (cyclic _ _).trans (by rw [hinitial, normalized])
  simp [he, normalized] at h

end Trace

/-- Row-weight scaling proves the spectral-radius conclusion from the
nonnegative edge-count matrix and its positive superinvariant vector. -/
private theorem prefix_spectral_radius_nonempty {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (M : Matrix V V ℕ) (w : V → ℝ)
    (hw : ∀ v, 0 < w v)
    (hbound : ∀ v, (∑ u, (M v u : ℝ) * w u) ≤ w v) :
    spectralRadius ℂ (A := Matrix V V ℂ) (fun v u => (M v u : ℂ)) ≤ 1 := by
  let A : Matrix V V ℂ := fun v u => M v u
  let D : (Matrix V V ℂ)ˣ :=
    ⟨Matrix.diagonal (fun v => (w v : ℂ)), Matrix.diagonal (fun v => (w v : ℂ)⁻¹),
      by
        rw [Matrix.diagonal_mul_diagonal]
        rw [← Matrix.diagonal_one]
        congr 1
        funext v
        exact mul_inv_cancel₀ (by exact_mod_cast (hw v).ne'),
      by
        rw [Matrix.diagonal_mul_diagonal]
        rw [← Matrix.diagonal_one]
        congr 1
        funext v
        exact inv_mul_cancel₀ (by exact_mod_cast (hw v).ne')⟩
  let B : Matrix V V ℂ := (↑D⁻¹ : Matrix V V ℂ) * A * (D : Matrix V V ℂ)
  have hnorm : ‖B‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun v _ => ?_
    have hent (u : V) : ‖B v u‖ = (w v)⁻¹ * ((M v u : ℝ) * w u) := by
      change ‖(Matrix.diagonal (fun v => (w v : ℂ)⁻¹) * A *
        Matrix.diagonal (fun v => (w v : ℂ))) v u‖ = _
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, norm_mul, norm_inv]
      simp [A, Real.norm_eq_abs, abs_of_pos (hw v), abs_of_pos (hw u), mul_assoc]
    change ((∑ u, ‖B v u‖₊ : NNReal) : ℝ) ≤ 1
    simp only [NNReal.coe_sum, coe_nnnorm, hent, ← Finset.mul_sum]
    calc
      _ ≤ (w v)⁻¹ * w v := mul_le_mul_of_nonneg_left (hbound v) (inv_nonneg.mpr (hw v).le)
      _ = 1 := inv_mul_cancel₀ (hw v).ne'
  have hs : spectralRadius ℂ B = spectralRadius ℂ A := by
    unfold spectralRadius
    rw [show spectrum ℂ B = spectrum ℂ A from spectrum.units_conjugate']
  change spectralRadius ℂ A ≤ 1
  rw [← hs]
  exact (spectrum.spectralRadius_le_nnnorm B).trans (by exact_mod_cast hnorm)

theorem prefix_spectral_radius {V : Type*} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℕ) (w : V → ℝ)
    (hw : ∀ v, 0 < w v)
    (hbound : ∀ v, (∑ u, (M v u : ℝ) * w u) ≤ w v) :
    spectralRadius ℂ (A := Matrix V V ℂ) (fun v u => (M v u : ℂ)) ≤ 1 := by
  rcases isEmpty_or_nonempty V with h | h
  · letI := h
    unfold spectralRadius
    rw [spectrum.of_subsingleton]
    simp
  · exact prefix_spectral_radius_nonempty M w hw hbound

/-- The actual adjacency matrix counts edges by source and target. -/
def edgeCounts {V : Type*} [DecidableEq V] (E : V → Type*) [∀ v, Fintype (E v)]
    (target : ∀ v, E v → V) : Matrix V V ℕ :=
  fun v u => (Finset.univ.filter fun e => target v e = u).card

/-- A faithful finite positive trace gives a positive superinvariant vector
for the actual edge-count matrix and bounds its spectral radius. -/
theorem finite_cyclic_prefix_records {A V : Type*} [Ring A] [StarRing A]
    [Fintype V] [DecidableEq V] (E : V → Type*) [∀ v, Fintype (E v)]
    (target : ∀ v, E v → V) (p : V → A) (S : ∀ v, E v → A) (τ : A →+ ℝ)
    (positive : ∀ a, 0 ≤ τ (star a * a))
    (faithful : ∀ a, τ (star a * a) = 0 → a = 0)
    (cyclic : ∀ a b, τ (a * b) = τ (b * a))
    (hne : ∀ v, p v ≠ 0) (hp : ∀ v, p v * p v = p v) (hps : ∀ v, star (p v) = p v)
    (hinitial : ∀ v e, star (S v e) * S v e = p (target v e))
    (hleft : ∀ v e, p v * (S v e * star (S v e)) = S v e * star (S v e))
    (hidempotent : ∀ v e, (S v e * star (S v e)) * (S v e * star (S v e)) =
        S v e * star (S v e))
    (horth : ∀ v (e f : E v), e ≠ f →
        (S v e * star (S v e)) * (S v f * star (S v f)) = 0) :
    (∀ v, 0 < τ (p v)) ∧
    (∀ v, (∑ u, (edgeCounts E target v u : ℝ) * τ (p u)) ≤ τ (p v)) ∧
    spectralRadius ℂ (A := Matrix V V ℂ) (fun v u => (edgeCounts E target v u : ℂ)) ≤ 1 := by
  have hpos (v : V) : 0 < τ (p v) := by
    have h (a : A) (ha : a ≠ 0) : 0 < τ (star a * a) :=
      lt_of_le_of_ne (positive a) fun he => ha (faithful a he.symm)
    simpa only [hps, hp] using h (p v) (hne v)
  have hweight := prefix_trace_weights E target p S τ positive cyclic hp hps
    hinitial hleft hidempotent horth
  have hrow (v : V) : (∑ u, (edgeCounts E target v u : ℝ) * τ (p u)) ≤ τ (p v) := by
    calc
      _ = ∑ u, ∑ e ∈ Finset.univ.filter (fun e => target v e = u), τ (p (target v e)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [show (edgeCounts E target v u : ℝ) * τ (p u) =
          ∑ _e ∈ Finset.univ.filter (fun e => target v e = u), τ (p u) by
            simp only [edgeCounts, Finset.sum_const, nsmul_eq_mul]]
        refine Finset.sum_congr rfl fun e he => ?_
        rw [(Finset.mem_filter.mp he).2]
      _ = ∑ e, τ (p (target v e)) := Finset.sum_fiberwise _ _ _
      _ ≤ τ (p v) := hweight v
  exact ⟨hpos, hrow, prefix_spectral_radius _ _ hpos hrow⟩

end UV.RevisionPrefixTrace
