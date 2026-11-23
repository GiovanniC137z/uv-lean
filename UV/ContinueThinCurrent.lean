import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The arclength Fourier current in a normalized Euclidean four-plane.
The signed pieces include the result of combining collinear retracings. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace Topology ENNReal

namespace UV

abbrev ThinCurrentPlane := EuclideanSpace ℝ (Fin 4)

/-- A signed straight segment with its actual unit arclength tangent. -/
structure ThinCurrentSegment where
  start : ThinCurrentPlane
  tangent : ThinCurrentPlane
  unit_tangent : ‖tangent‖ = 1
  length : ℝ
  length_nonneg : 0 ≤ length
  multiplicity : ℤ

def ThinCurrentSegment.point (e : ThinCurrentSegment) (s : ℝ) : ThinCurrentPlane :=
  e.start + s • e.tangent

def ThinCurrentSegment.finish (e : ThinCurrentSegment) : ThinCurrentPlane :=
  e.point e.length

/-- The oriented boundary vanishes, stated after testing against any
complex function. This includes polygonal cancellation and retracing. -/
def thinCurrentClosed {ι : Type*} [Fintype ι] (edges : ι → ThinCurrentSegment) : Prop :=
  ∀ f : ThinCurrentPlane → ℂ, (∑ j, (edges j).multiplicity *
    (f (edges j).finish - f (edges j).start)) = 0

def thinPlaneWave (p x : ThinCurrentPlane) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ p x : ℂ))

def thinCurrentSegmentWave (e : ThinCurrentSegment) (p : ThinCurrentPlane) : ℂ :=
  ∫ s in 0..e.length, thinPlaneWave p (e.point s)

/-- The vector Fourier line integral, in the four orthonormal physical
coordinates of the chosen plane. -/
def thinCurrent {ι : Type*} [Fintype ι] (edges : ι → ThinCurrentSegment)
    (p : ThinCurrentPlane) (k : Fin 4) : ℂ :=
  ∑ j, (edges j).multiplicity * ((edges j).tangent k : ℂ) * thinCurrentSegmentWave (edges j) p

def thinCurrentNormSq {ι : Type*} [Fintype ι] (edges : ι → ThinCurrentSegment)
    (p : ThinCurrentPlane) : ℝ :=
  ∑ k, ‖thinCurrent edges p k‖ ^ 2

theorem thinCurrentNormSq_nonneg {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment) (p : ThinCurrentPlane) :
    0 ≤ thinCurrentNormSq edges p := Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem thinSegmentWave_hasDerivAt (e : ThinCurrentSegment) (p : ThinCurrentPlane) (s : ℝ) :
    HasDerivAt (fun t : ℝ => thinPlaneWave p (e.point t))
      ((Complex.I * (inner ℝ p e.tangent : ℂ)) * thinPlaneWave p (e.point s)) s := by
  have hphase : (fun t : ℝ => thinPlaneWave p (e.point t)) =
      fun t : ℝ => Complex.exp (Complex.I * ((inner ℝ p e.start : ℂ) +
        (t : ℂ) * (inner ℝ p e.tangent : ℂ))) := by
    funext t
    simp [thinPlaneWave, ThinCurrentSegment.point, inner_add_right, real_inner_smul_right]
  rw [hphase]
  have ht := hasDerivAt_id (s : ℂ)
  have h1 := (ht.mul_const (inner ℝ p e.tangent : ℂ)).const_add (inner ℝ p e.start : ℂ)
  have h2 := (h1.const_mul Complex.I).cexp.comp_ofReal
  have he : thinPlaneWave p (e.point s) =
      Complex.exp (Complex.I * ((inner ℝ p e.start : ℂ) + (s : ℂ) * (inner ℝ p e.tangent : ℂ))) :=
    congrFun hphase s
  simpa only [one_mul, he, mul_comm] using h2

/-- Taking the momentum contraction of one segment yields its exact
endpoint difference, with the stipulated Fourier sign. -/
theorem thinCurrentSegment_contraction (e : ThinCurrentSegment) (p : ThinCurrentPlane) :
    Complex.I * (inner ℝ p e.tangent : ℂ) * thinCurrentSegmentWave e p =
      thinPlaneWave p e.finish - thinPlaneWave p e.start := by
  have hcont : Continuous (fun s : ℝ => thinPlaneWave p (e.point s)) :=
    continuous_iff_continuousAt.mpr fun s => (thinSegmentWave_hasDerivAt e p s).continuousAt
  have hint : IntervalIntegrable (fun s : ℝ =>
      (Complex.I * (inner ℝ p e.tangent : ℂ)) * thinPlaneWave p (e.point s)) volume 0 e.length :=
    (continuous_const.mul hcont).intervalIntegrable (μ := volume) (0 : ℝ) e.length
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => thinSegmentWave_hasDerivAt e p s) hint
  rw [intervalIntegral.integral_const_mul] at hh
  simpa [thinCurrentSegmentWave, ThinCurrentSegment.finish, ThinCurrentSegment.point] using hh

/-- A closed signed polygon has no longitudinal component at any
momentum, before any shell or spectral comparison is applied. -/
theorem thinCurrent_transverse {ι : Type*} [Fintype ι]
    (edges : ι → ThinCurrentSegment) (closed : thinCurrentClosed edges) (p : ThinCurrentPlane) :
    (∑ k, (p k : ℂ) * thinCurrent edges p k) = 0 := by
  have h := closed (thinPlaneWave p)
  simp_rw [← thinCurrentSegment_contraction] at h
  have hsum :
      Complex.I * (∑ k, (p k : ℂ) * thinCurrent edges p k) =
        ∑ j, (edges j).multiplicity * (Complex.I * (inner ℝ p (edges j).tangent : ℂ) *
          thinCurrentSegmentWave (edges j) p) := by
    simp only [thinCurrent, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Complex.ofReal_sum,
      Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  exact (mul_eq_zero.mp (hsum.trans h)).resolve_left Complex.I_ne_zero

end UV
