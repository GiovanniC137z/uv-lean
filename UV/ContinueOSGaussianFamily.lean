import UV.ContinueOSGaussianGram
import Mathlib.MeasureTheory.Constructions.Projective

/-! Consistent finite Gaussian distributions on every boundary and
point observable of the fixed-depth scalar model. -/

noncomputable section
open MeasureTheory Matrix
open scoped Matrix

namespace UV

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {m r : ℝ}

def osQuarticFiniteLaw (hm : 0 < m) (hr : 0 < r) (s : ι → OSQuarticSlot) : Measure (ι → ℝ) :=
  MarkedPhoton.photonProjectionLaw _ (osQuarticCovariance_posSemidef hm hr s)

instance osQuarticFiniteLaw_probability (hm : 0 < m) (hr : 0 < r) (s : ι → OSQuarticSlot) :
    IsProbabilityMeasure (osQuarticFiniteLaw hm hr s) :=
  MarkedPhoton.physicalLaw_probability _ _

/-- Exact finite Gaussian characteristic function in the specified covariance. -/
theorem osQuarticFiniteLaw_characteristic (hm : 0 < m) (hr : 0 < r) (s : ι → OSQuarticSlot) (t : ι → ℝ) :
    MarkedPhoton.photonCharacteristic (osQuarticFiniteLaw hm hr s) t =
      Complex.exp (-((t ⬝ᵥ ((fun i j => osQuarticCovariance m r (s i) (s j)) *ᵥ t) : ℝ) : ℂ)/2) :=
  MarkedPhoton.projectionLaw_characteristic _ _ _

private def osPushTest (f : κ → ι) (t : κ → ℝ) (i : ι) : ℝ :=
  ∑ a, if f a = i then t a else 0

omit [DecidableEq κ] in
private theorem osPushTest_pair (f : κ → ι) (t : κ → ℝ) (x : ι → ℝ) :
    osPushTest f t ⬝ᵥ x = t ⬝ᵥ (x ∘ f) := by
  simp only [dotProduct,osPushTest,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

/-- Pushforward under any reindexing map of a finite Gaussian projection. -/
theorem osFiniteGaussian_map (D : Matrix ι ι ℝ) (hD : D.PosSemidef) (f : κ → ι)
    (hsmall : (D.submatrix f f).PosSemidef) :
    (MarkedPhoton.photonProjectionLaw D hD).map (fun x => x ∘ f) =
      MarkedPhoton.photonProjectionLaw (D.submatrix f f) hsmall := by
  have hmeas : Measurable (fun (x : ι → ℝ) => x ∘ f) := measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  apply MarkedPhoton.gaussian_projection_law_eq
  intro t
  let u := osPushTest f t
  have hchar : MarkedPhoton.photonCharacteristic ((MarkedPhoton.photonProjectionLaw D hD).map (fun x => x ∘ f)) t =
      MarkedPhoton.photonCharacteristic (MarkedPhoton.photonProjectionLaw D hD) u := by
    unfold MarkedPhoton.photonCharacteristic
    rw [integral_map hmeas.aemeasurable (by fun_prop)]
    simp only [u,osPushTest_pair]
  rw [hchar, MarkedPhoton.projectionLaw_characteristic]
  congr 3
  apply congrArg Complex.ofReal
  change u ⬝ᵥ (D *ᵥ u) = t ⬝ᵥ (D.submatrix f f *ᵥ t)
  rw [show u ⬝ᵥ (D *ᵥ u) = _ from osPushTest_pair f t _]
  congr 1
  funext a
  change D (f a) ⬝ᵥ osPushTest f t = (fun b => D (f a) (f b)) ⬝ᵥ t
  rw [dotProduct_comm,osPushTest_pair,dotProduct_comm]
  rfl

/-- Projecting along any map, including duplication of an observable,
produces the intrinsic Gaussian law of the resulting list of slots. -/
theorem osQuarticFiniteLaw_map (hm : 0 < m) (hr : 0 < r) (s : ι → OSQuarticSlot) (f : κ → ι) :
    (osQuarticFiniteLaw hm hr s).map (fun x => x ∘ f) = osQuarticFiniteLaw hm hr (s ∘ f) :=
  osFiniteGaussian_map _ _ f _

/-- A projective probability family on the actual continuum index set. -/
theorem osQuarticFiniteLaw_projective (hm : 0 < m) (hr : 0 < r) :
    IsProjectiveMeasureFamily (α := fun _ : OSQuarticSlot => ℝ)
      (fun J => @osQuarticFiniteLaw J _ (Classical.decEq _) _ _ hm hr Subtype.val) := by
  classical
  intro I J hJI
  exact (osQuarticFiniteLaw_map hm hr (fun a : I => a.1) (fun j : J => ⟨j.1,hJI j.2⟩)).symm

end UV
