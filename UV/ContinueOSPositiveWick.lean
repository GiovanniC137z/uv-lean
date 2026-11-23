import UV.ContinueOSGaussianExtension
import UV.ContinueOSGaussianWick
import UV.VerifyCurvaturePairings

/-! Wick moments under a single Gaussian probability measure for an arbitrary
positive real covariance kernel. -/

noncomputable section
open MeasureTheory Matrix

namespace UV

variable {α : Type}

private theorem osMonomial_coordinate_measurable {ι : Type*} (l : List ι) :
    Measurable (osMonomial (fun (i : ι) (z : ι → ℝ) => z i) l) := by
  induction l with
  | nil => exact measurable_const
  | cons i l ih => exact (measurable_pi_apply i).mul ih

theorem osMatrixGaussian_wick {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (hD : D.PosSemidef) :
    OSWickMoments (MarkedPhoton.photonProjectionLaw D hD) (fun (i : ι) (z : ι → ℝ) => z i) D := by
  let d := hD.1.eigenvalues
  let U : Matrix ι ι ℝ := hD.1.eigenvectorUnitary
  have hw := MarkedPhoton.osLinearGaussian_wick d hD.eigenvalues_nonneg U
  have hcov (i j : ι) : (∑ k, U i k*d k*U j k) = D i j := by
    have he : D = U*Matrix.diagonal d*star U := hD.1.spectral_theorem
    rw [he,Matrix.mul_apply]
    simp only [Matrix.mul_diagonal,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,star_trivial]
  have hmean (l : List ι) : (∫ z, osMonomial (fun (i : ι) (z : ι → ℝ) => z i) l z ∂MarkedPhoton.photonProjectionLaw D hD) =
      ∫ z, osMonomial (fun b z => ∑ i, U b i*z i) l z ∂MarkedPhoton.coordinateLaw d :=
    integral_map (by fun_prop : AEMeasurable U.mulVec (MarkedPhoton.coordinateLaw d))
      (osMonomial_coordinate_measurable l).aestronglyMeasurable
  constructor
  · intro l
    apply (integrable_map_measure (osMonomial_coordinate_measurable l).aestronglyMeasurable
      (by fun_prop : AEMeasurable U.mulVec (MarkedPhoton.coordinateLaw d))).mpr
    exact hw.integrable l
  · intro n l hl
    rw [hmean,hw.moment n l hl]
    congr 1
    exact funext₂ hcov

theorem osPositiveFiniteLaw_wick (Q : OSPositiveCovariance α) {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι → α) :
    OSWickMoments (Q.law s) (fun (i : ι) (z : ι → ℝ) => z i) (fun i j => Q.entry (s i) (s j)) :=
  osMatrixGaussian_wick _ _

theorem osPositiveProcess_wick (Q : OSPositiveCovariance α)
    (μ : Measure (α → ℝ)) (hμ : IsProjectiveLimit (α := fun _ => ℝ) μ Q.family) :
    OSWickMoments μ (fun i z => z i) Q.entry := by
  classical
  have hlist (l : List α) (n : ℕ) (hn : l.length ≤ 2*n) :
      Integrable (osMonomial (fun (i : α) (z : α → ℝ) => z i) l) μ ∧
        (∫ z, osMonomial (fun (i : α) (z : α → ℝ) => z i) l z ∂μ) =
          osWickMoment (Q.entry) n l := by
    let J := l.toFinset
    let l' : List J := l.attach.map fun j => ⟨j.1,List.mem_toFinset.mpr j.2⟩
    have hl : l'.map Subtype.val = l := by
      simpa only [l',List.map_map,Function.comp_def] using List.attach_map_subtype_val l
    let E := osMonomial (fun (i : J) (z : J → ℝ) => z i) l'
    have hE : Measurable E := osMonomial_coordinate_measurable _
    have heq : osMonomial (fun (i : α) (z : α → ℝ) => z i) l = E ∘ J.restrict := by
      rw [←hl]
      funext z
      simp [E,osMonomial]
    have hfin := osPositiveFiniteLaw_wick Q (@Subtype.val _ (· ∈ J))
    have hp : μ.map J.restrict = Q.law (@Subtype.val _ (· ∈ J)) :=
      osPositiveGaussian_projection Q μ hμ (@Subtype.val _ (· ∈ J))
    have hi : Integrable E (μ.map J.restrict) := by
      rw [hp]
      exact hfin.integrable _
    rw [heq]
    refine ⟨hi.comp_aemeasurable (Finset.measurable_restrict J).aemeasurable,?_⟩
    have hInt : (∫ z, (E ∘ J.restrict) z ∂μ) = ∫ z, E z ∂μ.map J.restrict :=
      (integral_map (Finset.measurable_restrict J).aemeasurable hE.aestronglyMeasurable).symm
    rw [hInt,hp]
    have hlen : l'.length ≤ 2*n := by simpa [l'] using hn
    rw [show (∫ z, E z ∂Q.law (@Subtype.val _ (· ∈ J))) = _ from hfin.moment n l' hlen]
    simpa [hl] using VerifyCurvaturePairings.osWickMoment_scaled (Q.entry)
      (@Subtype.val _ (· ∈ J)) (fun _ => 1) n l'
  exact ⟨fun l => (hlist l l.length (by omega)).1,fun n l hl => (hlist l n hl).2⟩

/-- Restricting a Wick field along an arbitrary probe map preserves
every finite product moment, including repeated slots. -/
theorem OSWickMoments.reindex {Ω α β : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : α → Ω → ℝ} {K : α → α → ℝ} (hW : OSWickMoments μ F K) (f : β → α) :
    OSWickMoments μ (F ∘ f) (fun i j => K (f i) (f j)) := by
  have he (l : List β) : osMonomial (F ∘ f) l = osMonomial F (l.map f) := by
    funext z
    simp [osMonomial,List.map_map,Function.comp_def]
  constructor
  · intro l
    rw [he]
    exact hW.integrable _
  · intro n l hlen
    rw [he,hW.moment n _ (by simpa using hlen)]
    symm
    simpa using VerifyCurvaturePairings.osWickMoment_scaled K f (fun _ => 1) n l

end UV
