import UV.ContinueThinCurrent
import UV.ContinuationSectorPlane

/-! The exact four sides of the rectangular Wilson contour on an intrinsic
spatial torus. The GT coordinate is constant along every side. -/

noncomputable section

open MeasureTheory Set Real
open scoped RealInnerProductSpace Interval

namespace UV

private def rectAxis (j : Fin 4) : ThinCurrentPlane := EuclideanSpace.single j 1

private def opticalRectEdge (x : ThinCurrentPlane) (j : Fin 4) (a : ℝ) (ha : 0 ≤ a) (s : ℤ) :
    ThinCurrentSegment := ⟨x, rectAxis j, by simp [rectAxis], a, ha, s⟩

/-- Counterclockwise contour. The third and fourth sides use signed
multiplicity and the same unit arclength tangents as the opposite sides. -/
def opticalRectEdges {L h : ℝ} (hL : 0 < L) (hh : 0 < h) : Fin 4 → ThinCurrentSegment :=
  ![opticalRectEdge 0 1 h hh.le 1, opticalRectEdge (h • rectAxis 1) 2 (L/2) (half_pos hL).le 1,
    opticalRectEdge ((L/2) • rectAxis 2) 1 h hh.le (-1), opticalRectEdge 0 2 (L/2) (half_pos hL).le (-1)]

theorem opticalRect_closed {L h : ℝ} (hL : 0 < L) (hh : 0 < h) :
    thinCurrentClosed (opticalRectEdges hL hh) := by
  intro f
  simp [Fin.sum_univ_four, opticalRectEdges, opticalRectEdge, ThinCurrentSegment.finish, ThinCurrentSegment.point,
    add_comm (h • rectAxis 1) ((L/2) • rectAxis 2)]

/-- Full physical torus momentum embedded at zero GT frequency. -/
def opticalTorusMode (L : ℝ) (n : Fin 3 → ℤ) : ThinCurrentPlane :=
  WithLp.toLp 2 ![0, (2*π/L)*(n 0 : ℝ), (2*π/L)*(n 1 : ℝ), (2*π/L)*(n 2 : ℝ)]

private theorem rectInner (p : ThinCurrentPlane) (j : Fin 4) : ⟪p, rectAxis j⟫ = p j := by
  simp [rectAxis, EuclideanSpace.inner_single_right]

private theorem rectWave (p : ThinCurrentPlane) (x : ThinCurrentPlane) (j : Fin 4) (a : ℝ)
    (ha : 0 ≤ a) (s : ℤ) : thinCurrentSegmentWave (opticalRectEdge x j a ha s) p =
      thinPlaneWave p x * ∫ t in 0..a, Complex.exp (Complex.I * ((t * p j : ℝ) : ℂ)) := by
  unfold thinCurrentSegmentWave ThinCurrentSegment.point
  simp only [opticalRectEdge, thinPlaneWave, inner_add_right, real_inner_smul_right, rectInner,
    Complex.ofReal_add, mul_add, Complex.exp_add]
  exact intervalIntegral.integral_const_mul _ _

private theorem rectWave_origin (p : ThinCurrentPlane) : thinPlaneWave p 0 = 1 := by simp [thinPlaneWave]

private theorem rectWave_axis (p : ThinCurrentPlane) (j : Fin 4) (a : ℝ) :
    thinPlaneWave p (a • rectAxis j) = Complex.exp (Complex.I * ((a * p j : ℝ) : ℂ)) := by
  simp [thinPlaneWave, real_inner_smul_right, rectInner]

/-- At zero first spatial momentum, the contributions from the two
axis-two segments cancel before taking a transverse projection. -/
theorem opticalRect_current {L h : ℝ} (hL : 0 < L) (hh : 0 < h)
    (p : ThinCurrentPlane) (hp : p 1 = 0) (j : Fin 4) :
    thinCurrent (opticalRectEdges hL hh) p j =
      ((rectAxis 1 j : ℝ) : ℂ) * h * (1 - Complex.exp (Complex.I * (((L/2) * p 2 : ℝ) : ℂ))) := by
  rw [thinCurrent, Fin.sum_univ_four]
  have e0 : opticalRectEdges hL hh 0 = opticalRectEdge 0 1 h hh.le 1 := rfl
  have e1 : opticalRectEdges hL hh 1 = opticalRectEdge (h • rectAxis 1) 2 (L/2) (half_pos hL).le 1 := rfl
  have e2 : opticalRectEdges hL hh 2 = opticalRectEdge ((L/2) • rectAxis 2) 1 h hh.le (-1) := rfl
  have e3 : opticalRectEdges hL hh 3 = opticalRectEdge 0 2 (L/2) (half_pos hL).le (-1) := rfl
  rw [e0,e1,e2,e3]
  simp only [rectWave]
  simp [opticalRectEdge, rectWave_origin, rectWave_axis, hp]
  ring

theorem opticalRect_odd_wave {L : ℝ} (hL : 0 < L) (b c : ℤ) :
    Complex.exp (Complex.I * (((L/2) * opticalTorusMode L ![0, 2*b+1, c] 2 : ℝ) : ℂ)) = -1 := by
  have h : (L/2) * opticalTorusMode L ![0, 2*b+1, c] 2 = (b : ℝ)*(2*π) + π := by
    simp [opticalTorusMode]
    field_simp
  rw [h]
  push_cast
  rw [show Complex.I * ((b : ℂ)*(2*π) + π) = (b:ℂ)*(2*π*Complex.I) + π*Complex.I by ring,
    Complex.exp_add_pi_mul_I, Complex.exp_int_mul_two_pi_mul_I]

theorem opticalRect_odd_current {L h : ℝ} (hL : 0 < L) (hh : 0 < h) (b c : ℤ) (j : Fin 4) :
    thinCurrent (opticalRectEdges hL hh) (opticalTorusMode L ![0,2*b+1,c]) j =
      if j = 1 then (2*h : ℂ) else 0 := by
  rw [opticalRect_current hL hh _ (by simp [opticalTorusMode]), opticalRect_odd_wave hL]
  by_cases hj : j = 1
  · simp [rectAxis, EuclideanSpace.single_apply, hj]
    ring
  · simp [rectAxis, EuclideanSpace.single_apply, hj]

theorem opticalRect_odd_normSq {L h : ℝ} (hL : 0 < L) (hh : 0 < h) (b c : ℤ) :
    thinCurrentNormSq (opticalRectEdges hL hh) (opticalTorusMode L ![0,2*b+1,c]) = (2*h)^2 := by
  simp [thinCurrentNormSq, Fin.sum_univ_four, opticalRect_odd_current,
    Real.norm_eq_abs, abs_of_pos hh]

theorem opticalRect_transverse {L h : ℝ} (hL : 0 < L) (hh : 0 < h) (n : Fin 3 → ℤ) :
    ∑ j : Fin 4, ((opticalTorusMode L n j : ℝ) : ℂ) *
      thinCurrent (opticalRectEdges hL hh) (opticalTorusMode L n) j = 0 :=
  thinCurrent_transverse _ (opticalRect_closed hL hh) _

end UV
