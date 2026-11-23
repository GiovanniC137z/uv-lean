import UV.ContinueWilsonReturnCurrent
import UV.ContinueWilsonLinkMarks

/-! Source derivatives of the product of straight Wilson phases, on the
finite Fourier family of the external field. Each plane wave has its own
complex amplitude and a real unit polarization. The background is real. -/

noncomputable section

open MeasureTheory UV.SectorPlane
open scoped RealInnerProductSpace BigOperators unitInterval

namespace UV

variable {a N n : ℕ}

/-- Evaluate the unexpanded path exponentials in a superposition of fixed
Fourier modes. Complex amplitudes give the multilinear extension from
real fields. The affine path on each link starts at its previous vertex. -/
def wilsonFourierLinks (B : WilsonContinuousConnection) (d : Fin N → OSFourSpace)
    (u : Fin a → UnitVector OSFourSpace) (p : Fin a → OSFourSpace) (t : Fin a → ℂ) : ℂ :=
  ∏ j, Complex.exp (Complex.I * ((wilsonLineIntegral B (wilsonFiniteStart d j) (d j) : ℂ) +
    ∫ s in (0:ℝ)..1, ∑ i, t i * thinPlaneWave (p i) (wilsonFiniteStart d j + s • d j) *
      (⟪(u i).val,d j⟫ : ℝ)))

theorem wilson_fourier_links_factor (B : WilsonContinuousConnection) (d : Fin N → OSFourSpace)
    (u : Fin a → UnitVector OSFourSpace) (p : Fin a → OSFourSpace) (t : Fin a → ℂ) :
    wilsonFourierLinks B d u p t = (∏ j, wilsonLinkPhase B (wilsonFiniteStart d j) (d j)) *
      Complex.exp (Complex.I * ∑ i, t i * wilsonFiniteMark d (u i) (p i)) := by
  have hi (j : Fin N) (i : Fin a) : IntervalIntegrable (fun s : ℝ =>
      t i * thinPlaneWave (p i) (wilsonFiniteStart d j+s • d j) * (⟪(u i).val,d j⟫:ℝ)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold thinPlaneWave
    fun_prop
  have hs (j : Fin N) : (∫ s in (0:ℝ)..1, ∑ i, t i * thinPlaneWave (p i) (wilsonFiniteStart d j+s • d j) *
      (⟪(u i).val,d j⟫:ℝ)) = ∑ i, t i * (wilsonEdgeWave (p i) (wilsonFiniteStart d j) (d j) * (⟪(u i).val,d j⟫:ℝ)) := by
    rw [intervalIntegral.integral_finset_sum (fun i _ => hi j i)]
    simp only [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,wilsonEdgeWave,mul_assoc]
  simp only [wilsonFourierLinks,hs,mul_add,Complex.exp_add,Finset.prod_mul_distrib,wilsonLinkPhase,←Complex.exp_sum]
  congr 2
  rw [←Finset.mul_sum,Finset.sum_comm]
  simp only [wilsonFiniteMark,Finset.mul_sum]

/-- Repeated directional differentiation in the complex amplitude of each
labelled mode, including repetitions of the same label. -/
def wilsonModeVariation : List (Fin a) → ((Fin a → ℂ) → ℂ) → (Fin a → ℂ) → ℂ
  | [], F, t => F t
  | i :: l, F, t => deriv (fun r : ℂ => wilsonModeVariation l F (t + Pi.single i r)) 0

private theorem wilson_modes_deriv (c : ℂ) (M t : Fin a → ℂ) (i : Fin a) :
    HasDerivAt (fun r : ℂ => c * Complex.exp (Complex.I * ∑ j, ((t + Pi.single i r : Fin a → ℂ) j) * M j))
      ((Complex.I*M i)*(c*Complex.exp (Complex.I*∑ j, t j*M j))) 0 := by
  have hs (r : ℂ) : (∑ j, ((t + Pi.single i r : Fin a → ℂ) j) * M j) = (∑ j, t j*M j) + r*M i := by
    simp [Pi.add_apply,add_mul,Finset.sum_add_distrib,Pi.single_apply,ite_mul]
  simp_rw [hs]
  have h := (((((hasDerivAt_id (0:ℂ)).mul_const (M i)).const_add (∑ j, t j*M j)).const_mul Complex.I).cexp).const_mul c
  simpa only [id_eq,one_mul,zero_mul,mul_zero,add_zero,mul_assoc,mul_left_comm,mul_comm] using h

theorem wilson_fourier_links_derivative (B : WilsonContinuousConnection) (d : Fin N → OSFourSpace)
    (u : Fin a → UnitVector OSFourSpace) (p : Fin a → OSFourSpace) (t : Fin a → ℂ) (i : Fin a) :
    HasDerivAt (fun r : ℂ => wilsonFourierLinks B d u p (t + Pi.single i r))
      ((Complex.I*wilsonFiniteMark d (u i) (p i))*wilsonFourierLinks B d u p t) 0 := by
  simp_rw [wilson_fourier_links_factor]
  exact wilson_modes_deriv _ (fun j => wilsonFiniteMark d (u j) (p j)) t i

theorem wilson_polygon_source_variations (B : WilsonContinuousConnection) (d : Fin N → OSFourSpace)
    (u : Fin a → UnitVector OSFourSpace) (p : Fin a → OSFourSpace) (l : List (Fin a)) (t : Fin a → ℂ) :
    wilsonModeVariation l (wilsonFourierLinks B d u p) t =
      (l.map (fun i => Complex.I*wilsonFiniteMark d (u i) (p i))).prod * wilsonFourierLinks B d u p t := by
  induction l generalizing t with
  | nil => simp [wilsonModeVariation]
  | cons i l ih =>
    simp only [wilsonModeVariation,ih,List.map_cons,List.prod_cons]
    rw [((wilson_fourier_links_derivative B d u p t i).const_mul _).deriv]
    ring

/-- At zero background the actual derivative of the spin-weighted
polygon phase agrees, including its power of i, with all placements
integrated over the independent straight-link fractions. -/
theorem wilson_source_variations_eq_placements {ι : Type*} [Fintype ι] (L : ℝ)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) (u : Fin a → UnitVector OSFourSpace)
    (p : Fin a → OSFourSpace) (d : Fin n → OSFourSpace) :
    wilsonReturnWeight L T d * wilsonModeVariation (List.ofFn (fun i : Fin a => i))
      (wilsonFourierLinks 0 (wilsonReturnSteps d) u p) 0 =
      Complex.I^a * (∑ f : Fin a → Fin (n+1), ∫ s : Fin a → unitInterval, wilsonMarkedReturn L T
        (fun j => (wilsonAssignedHop u f (wilsonVisitShift f s p) j).marks) (wilsonVisitShift f s p) d) := by
  rw [wilson_polygon_source_variations,wilson_polygon_all_placements,wilson_fourier_links_factor]
  simp only [List.map_ofFn,List.prod_ofFn,Function.comp_apply,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,Pi.zero_apply,zero_mul,Finset.sum_const_zero,mul_zero,Complex.exp_zero,mul_one]
  have hw (j : Fin (n+1)) : wilsonLinkPhase (0 : WilsonContinuousConnection) (wilsonFiniteStart (wilsonReturnSteps d) j)
      (wilsonReturnSteps d j) = 1 := by simp [wilsonLinkPhase,wilsonLineIntegral]
  simp only [hw,Finset.prod_const_one,mul_one]
  ring

end UV
