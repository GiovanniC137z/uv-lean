import UV.BernsteinContourHomotopy
import UV.BernsteinContourTensor

/-! Exact boundary identification connects the genuine smooth tensor
homotopies to the uniformly Lipschitz Bernstein curves used for contour
integral limits. -/

noncomputable section
open Set
open scoped unitInterval NNReal

namespace UV

theorem bernsteinTensorExtension_start_eq (n : ℕ) (H : C(I, C(I, ℂ)))
    (f : ℝ → ℂ) (hsource : ∀ t : I, H 0 t = f t) {t : ℝ} (ht : t ∈ Icc 0 1) :
    bernsteinTensorExtension (n+1) (n+1) H (0,t) = bernsteinCurveExtension (n+1) f t := by
  let x : I := ⟨t,ht⟩
  have h := bernsteinTensorExtension_eq (n+1) (n+1) H (0:I) x
  rw [bernsteinTensor_start] at h
  exact h.trans (bernsteinCurveExtension_eq_approximation (n+1) f (H 0)
    (fun t => (hsource t).symm) x).symm

theorem bernsteinTensorExtension_end_eq (n : ℕ) (H : C(I, C(I, ℂ)))
    (f : ℝ → ℂ) (hsource : ∀ t : I, H 1 t = f t) {t : ℝ} (ht : t ∈ Icc 0 1) :
    bernsteinTensorExtension (n+1) (n+1) H (1,t) = bernsteinCurveExtension (n+1) f t := by
  let x : I := ⟨t,ht⟩
  have h := bernsteinTensorExtension_eq (n+1) (n+1) H (1:I) x
  rw [bernsteinTensor_end (Nat.succ_ne_zero n)] at h
  exact h.trans (bernsteinCurveExtension_eq_approximation (n+1) f (H 1)
    (fun t => (hsource t).symm) x).symm

theorem bernsteinTensorExtension_start_lipschitzOnWith {K : ℝ≥0}
    (n : ℕ) (H : C(I, C(I, ℂ))) (f : ℝ → ℂ)
    (hsource : ∀ t : I, H 0 t = f t) (hLip : LipschitzOnWith K f (Icc 0 1)) :
    LipschitzOnWith K (fun t => bernsteinTensorExtension (n+1) (n+1) H (0,t)) (Icc 0 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [bernsteinTensorExtension_start_eq n H f hsource hx,
    bernsteinTensorExtension_start_eq n H f hsource hy]
  exact (bernsteinCurveExtension_lipschitzOnWith hLip n).dist_le_mul x hx y hy

theorem bernsteinTensorExtension_end_lipschitzOnWith {K : ℝ≥0}
    (n : ℕ) (H : C(I, C(I, ℂ))) (f : ℝ → ℂ)
    (hsource : ∀ t : I, H 1 t = f t) (hLip : LipschitzOnWith K f (Icc 0 1)) :
    LipschitzOnWith K (fun t => bernsteinTensorExtension (n+1) (n+1) H (1,t)) (Icc 0 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [bernsteinTensorExtension_end_eq n H f hsource hx,
    bernsteinTensorExtension_end_eq n H f hsource hy]
  exact (bernsteinCurveExtension_lipschitzOnWith hLip n).dist_le_mul x hx y hy

theorem bernsteinTensorExtension_closed (n : ℕ) (H : C(I, C(I, ℂ)))
    (hclosed : ∀ s : I, H s 0 = H s 1) {s : ℝ} (hs : s ∈ Icc 0 1) :
    bernsteinTensorExtension (n+1) (n+1) H (s,0) =
      bernsteinTensorExtension (n+1) (n+1) H (s,1) := by
  let x : I := ⟨s,hs⟩
  rw [show (s,0) = ((x:ℝ),((0:I):ℝ)) by rfl,
    show (s,1) = ((x:ℝ),((1:I):ℝ)) by rfl,
    bernsteinTensorExtension_eq, bernsteinTensorExtension_eq]
  exact bernsteinTensor_closed (Nat.succ_ne_zero n) H hclosed x

end UV
