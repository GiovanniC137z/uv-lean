import UV.ContinueOSGaussianFamily
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Kernel.Composition.Lemmas

/-! Construction of the free Gaussian law on any countable sequence of
boundary and transferred point slots using conditional transition kernels. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Finset Preorder
open scoped ENNReal

namespace UV

private abbrev osHist (n : ℕ) := Iic n → ℝ

private def osAppend (n : ℕ) : osHist n × ℝ ≃ᵐ osHist (n+1) :=
  ((MeasurableEquiv.refl (osHist n)).prodCongr (MeasurableEquiv.piSingleton (X := fun _ => ℝ) n)).trans
    (MeasurableEquiv.IicProdIoc (X := fun _ => ℝ) (Nat.le_succ n))

private theorem osCountableExtension (P : (I : Finset ℕ) → Measure (I → ℝ))
    [∀ I, IsProbabilityMeasure (P I)] (hP : IsProjectiveMeasureFamily (α := fun _ => ℝ) P) :
    ∃ μ : Measure (ℕ → ℝ), IsProjectiveLimit μ P := by
  let Q (n : ℕ) := (P (Iic (n+1))).map (osAppend n).symm
  haveI hQ (n : ℕ) : IsProbabilityMeasure (Q n) := isProbabilityMeasure_map (osAppend n).symm.measurable.aemeasurable
  let κ (n : ℕ) := (Q n).condKernel
  haveI hκ (n : ℕ) : IsMarkovKernel (κ n) := inferInstanceAs (IsMarkovKernel (Q n).condKernel)
  have hfst (n : ℕ) : (Q n).fst = P (Iic n) := by
    dsimp only [Q,Measure.fst]
    rw [map_map measurable_fst (osAppend n).symm.measurable]
    exact (hP _ _ (Finset.Iic_subset_Iic.mpr n.le_succ)).symm
  have hstep (n : ℕ) : Kernel.partialTraj (X := fun _ => ℝ) κ n (n+1) ∘ₘ P (Iic n) = P (Iic (n+1)) := by
    rw [Kernel.partialTraj_succ_self,←Measure.map_comp _ _ (measurable_IicProdIoc (X := fun _ : ℕ => ℝ) (m := n) (n := n+1)),
      ←Measure.compProd_eq_comp_prod,Measure.compProd_map (μ := P (Iic n)) (κ := κ n) (MeasurableEquiv.piSingleton (X := fun _ => ℝ) n).measurable,
      ←hfst n,show (Q n).fst ⊗ₘ κ n = Q n from Measure.disintegrate _ _]
    rw [map_map (measurable_IicProdIoc (X := fun _ : ℕ => ℝ) (m := n) (n := n+1))
      (measurable_id.prodMap (MeasurableEquiv.piSingleton (X := fun _ => ℝ) n).measurable)]
    change (Q n).map (osAppend n) = _
    exact (osAppend n).symm.map_symm_map
  have hpartial (n : ℕ) : Kernel.partialTraj (X := fun _ => ℝ) κ 0 n ∘ₘ P (Iic 0) = P (Iic n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le _),←Measure.comp_assoc,ih,hstep]
  let μ := Kernel.traj (X := fun _ => ℝ) κ 0 ∘ₘ P (Iic 0)
  refine ⟨μ, (isProjectiveLimit_nat_iff hP μ).mpr ?_⟩
  intro n
  rw [show μ.map (frestrictLe n) = _ from Measure.map_comp _ _ (by fun_prop),Kernel.traj_map_frestrictLe]
  exact hpartial n

/-- Every countable sequence of Fourier observables has a common
probability space with the exact finite Gaussian laws on all coordinates. -/
theorem osQuarticCountableGaussian {m r : ℝ} (hm : 0 < m) (hr : 0 < r) (s : ℕ → OSQuarticSlot) :
    ∃ μ : Measure (ℕ → ℝ), IsProbabilityMeasure μ ∧
      IsProjectiveLimit (α := fun _ => ℝ) μ (fun J =>
        osQuarticFiniteLaw hm hr (fun j : J => s j)) := by
  let P (J : Finset ℕ) := osQuarticFiniteLaw hm hr (fun j : J => s j)
  haveI (J : Finset ℕ) : IsProbabilityMeasure (P J) := osQuarticFiniteLaw_probability _ _ _
  have hP : IsProjectiveMeasureFamily (α := fun _ => ℝ) P := by
    intro I J hJI
    exact (osQuarticFiniteLaw_map hm hr (fun a : I => s a) (fun j : J => ⟨j.1,hJI j.2⟩)).symm
  obtain ⟨μ,hμ⟩ := osCountableExtension P hP
  exact ⟨μ,hμ.isProbabilityMeasure,hμ⟩

end UV
