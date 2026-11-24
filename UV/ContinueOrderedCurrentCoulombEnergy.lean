import UV.ContinueOrderedCurrentCoulomb

/-! Absolute integration of the instantaneous quadratic energy in the
Hamiltonian order: first the spatial photon momentum, then carrier time. -/

noncomputable section

open MeasureTheory Finset
open scoped RealInnerProductSpace ComplexConjugate

namespace UV.SectorPlane.OrderedTwoBandPath

theorem measurable_timeDensity (P : OrderedTwoBandPath) :
    Measurable (fun z : ℝ × Spatial => P.timeDensity z.1 z.2) := by
  unfold timeDensity
  apply Finset.measurable_sum
  intro j _
  have hW : Continuous (fun z : ℝ × Spatial => spatialWave z.2 (P.position j)) := by unfold spatialWave; fun_prop
  apply hW.measurable.mul
  unfold occupation
  exact (Measurable.ite (measurableSet_le measurable_fst measurable_const) measurable_const measurable_const).sub
    (Measurable.ite (measurableSet_le measurable_fst measurable_const) measurable_const measurable_const)

def coulombEnergyDensity {ι : Type*} [Fintype ι] (P : ι → OrderedTwoBandPath)
    (c : ι → ℝ) (a : ℝ) (z : ℝ × Spatial) : ℝ :=
  coulombWeight a z.2 * Complex.normSq (∑ i, (c i:ℂ)*(P i).timeDensity z.1 z.2)

theorem coulombEnergyDensity_integrable {ι : Type*} [Fintype ι] (P : ι → OrderedTwoBandPath)
    (c : ι → ℝ) {a : ℝ} (ha : 0 < a) : Integrable (coulombEnergyDensity P c a) := by
  let F := fun i j (p : Spatial) (u : ℝ) => c i*c j*timeGram (P i) (P j) p u
  have hF (i j : ι) (p : Spatial) : Integrable (F i j p) := ((P i).timeGram_integrable (P j) p).const_mul _
  have he (p : Spatial) (u : ℝ) : coulombEnergyDensity P c a (u,p) =
      coulombWeight a p*(∑ i, ∑ j, F i j p u) := by rw [coulombEnergyDensity,←timeGram_energy]
  have hm : Measurable (coulombEnergyDensity P c a) := by
    apply (show Measurable (fun z : ℝ × Spatial => coulombWeight a z.2) by unfold coulombWeight; fun_prop).mul
    exact Complex.continuous_normSq.measurable.comp (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((P i).measurable_timeDensity))
  rw [Measure.volume_eq_prod]
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun p => by
      simp_rw [he]
      exact (integrable_finset_sum univ (fun i _ => integrable_finset_sum univ (fun j _ => hF i j p))).const_mul _
  · have hn (p : Spatial) (u : ℝ) : 0 ≤ coulombEnergyDensity P c a (u,p) :=
      mul_nonneg (by unfold coulombWeight; positivity) (Complex.normSq_nonneg _)
    have hnorm (x : ℝ) (y : Spatial) : ‖coulombEnergyDensity P c a (x,y)‖ = coulombEnergyDensity P c a (x,y) := Real.norm_of_nonneg (hn y x)
    simp_rw [hnorm]
    simp_rw [he,integral_const_mul,
      integral_finset_sum univ (fun i _ => integrable_finset_sum univ (fun j _ => hF i j _)),
      integral_finset_sum univ (fun j _ => hF _ j _),F,Finset.mul_sum]
    apply integrable_finset_sum
    intro i _
    apply integrable_finset_sum
    intro j _
    simp_rw [integral_const_mul]
    simpa only [mul_left_comm (c i*c j)] using ((P i).weightedGram_integrable (P j) ha).const_mul (c i*c j)

theorem coulomb_hamiltonian_characteristic {ι : Type} [Fintype ι] [DecidableEq ι]
    {a : ℝ} (ha : 0 < a) (μ : Measure (OrderedTwoBandPath → ℝ))
    (hμ : IsProjectiveLimit (α := fun _ => ℝ) μ (coulombGaussianKernel ha).family)
    (P : ι → OrderedTwoBandPath) (c : ι → ℝ) :
    (∫ x, Complex.exp (((∑ i, c i*x (P i):ℝ):ℂ)*Complex.I) ∂μ) =
      Complex.exp (-(((2*Real.pi)^(-3:ℤ) * ∫ t : ℝ, ∫ p : Spatial, coulombEnergyDensity P c a (t,p) : ℝ):ℂ)/2) := by
  have hi : Integrable (coulombEnergyDensity P c a) ((volume : Measure ℝ).prod volume) :=
    coulombEnergyDensity_integrable P c ha
  rw [←integral_prod _ hi,integral_prod_symm _ hi]
  simpa only [coulombEnergyDensity,integral_const_mul] using coulomb_gaussian_process_sewing ha μ hμ P c

end UV.SectorPlane.OrderedTwoBandPath
