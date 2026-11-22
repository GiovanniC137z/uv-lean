import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac

/-! Ordered two-point transfer on a common smearing domain. The integral below
is the admitted pairing of the Wightman kernels with the two transfer factors.
Both orderings use complementary weights, including at equal GT. -/

open MeasureTheory

namespace UV

/-- The ordering identity at the distributional pairing level. `θ` is
multiplication by the source step weight on the admitted common linear
domain, and `pair` is the two-kernel pairing. The output step weight is the
scalar `w`, and the complementary source weight is `1 - θ`. -/
theorem gt_ordered_distribution_transfer_sub_transfer_ordered {E : Type*}
    [AddCommGroup E] [Module ℂ E] (pair : E →ₗ[ℂ] ℂ) (θ : E →ₗ[ℂ] E)
    (w : ℂ) (forward backward : E) :
    pair (w • forward + (1 - w) • backward) - pair (θ forward + backward - θ backward) =
      pair (w • (forward - backward) - θ (forward - backward)) := by
  simp only [map_add, map_sub, map_smul, smul_eq_mul]
  ring

section Ordering

variable {X : Type*} [MeasurableSpace X]

/-- The integrand obtained by applying the two scalar transfer factors to a
pair of Wightman orders with the specified forward weight. -/
def gtOrderedTransferIntegrand (kₓ kᵧ : X → ℝ)
    (forward backward : X → ℂ) (weight : X → ℝ) (z : X) : ℂ :=
  ((kₓ z * kᵧ z : ℝ) : ℂ) *
    ((weight z : ℂ) * forward z + (1 - (weight z : ℂ)) * backward z)

/-- Exact transfer/ordering discrepancy on the common admitted domain. Use
`X = Y × Y` and `μ = ν.prod ν` for the two endpoint integrations. `w` is the
output step weight and `θ` is the step weight on the source endpoints. -/
theorem gt_ordered_transfer_sub_transfer_ordered (μ : Measure X)
    (kₓ kᵧ : X → ℝ) (forward backward : X → ℂ)
    (w : ℝ) (θ : X → ℝ)
    (hout : Integrable (gtOrderedTransferIntegrand kₓ kᵧ forward backward (fun _ => w)) μ)
    (hin : Integrable (gtOrderedTransferIntegrand kₓ kᵧ forward backward θ) μ) :
    (∫ z, gtOrderedTransferIntegrand kₓ kᵧ forward backward (fun _ => w) z ∂μ) -
      (∫ z, gtOrderedTransferIntegrand kₓ kᵧ forward backward θ z ∂μ) =
      ∫ z, ((kₓ z * kᵧ z : ℝ) : ℂ) * ((w - θ z : ℝ) : ℂ) *
        (forward z - backward z) ∂μ := by
  rw [← integral_sub hout hin]
  congr 1
  funext z
  simp only [gtOrderedTransferIntegrand, Complex.ofReal_sub]
  ring

/-- A transfer supported on equal order weights has no discrepancy. The
hypothesis states the support condition against the actual integration law. -/
theorem gt_ordered_transfer_eq_of_support (μ : Measure X)
    (kₓ kᵧ : X → ℝ) (forward backward : X → ℂ)
    (w : ℝ) (θ : X → ℝ)
    (hout : Integrable (gtOrderedTransferIntegrand kₓ kᵧ forward backward (fun _ => w)) μ)
    (hin : Integrable (gtOrderedTransferIntegrand kₓ kᵧ forward backward θ) μ)
    (hs : ∀ᵐ z ∂μ, kₓ z * kᵧ z = 0 ∨ θ z = w) :
    (∫ z, gtOrderedTransferIntegrand kₓ kᵧ forward backward (fun _ => w) z ∂μ) =
      ∫ z, gtOrderedTransferIntegrand kₓ kᵧ forward backward θ z ∂μ := by
  apply sub_eq_zero.mp
  rw [gt_ordered_transfer_sub_transfer_ordered μ kₓ kᵧ forward backward w θ hout hin]
  calc
    _ = ∫ _ : X, (0 : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hs] with z hz
      rcases hz with hz | hz <;> simp [hz]
    _ = 0 := integral_zero _ _

end Ordering

/-- A common scalar pairing with reversed source and output time orders
exhibits a nonzero discrepancy. -/
theorem gt_ordered_transfer_ne_example :
    (∫ z, gtOrderedTransferIntegrand (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 0)
      (fun _ => 1) z ∂(Measure.dirac (0 : ℝ))) -
    (∫ z, gtOrderedTransferIntegrand (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 0)
      (fun _ => 0) z ∂(Measure.dirac (0 : ℝ))) = (1 : ℂ) := by
  simp [gtOrderedTransferIntegrand]

end UV
