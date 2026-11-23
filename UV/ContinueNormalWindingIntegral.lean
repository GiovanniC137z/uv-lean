import UV.ContinueNormalWindingLoop

/-! Integrate the winding majorant jointly in all independent normal
increments and the carrier momentum. This formulation accepts both
Lebesgue and reciprocal-lattice carrier measures. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set UV.SectorPlane

namespace UV

variable {n : ℕ}

def normalWindingBudget (n : ℕ) (m L B : ℝ) :=
  L*(4*2^(n+1))*(8/m)^n*((n+1:ℕ)*B)

def normalWindingRate (m L : ℝ) (w : ℤ) := Real.exp (-(m/4)*|(w:ℝ)*L|)

theorem normal_winding_rate_summable {m L : ℝ} (hm : 0 < m) (hL : 0 < L) :
    Summable (normalWindingRate m L) := by
  have h := normal_winding_majorant (m := m/2) (by positivity) hL
  apply Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) _ h.1
  intro w
  simpa only [zero_add,show m/2/2=m/4 by ring] using h.2 0 (by simpa using hL.le) w

theorem normal_winding_trace_integral {m L : ℝ} (hm : 0 < m) (hL : 0 < L)
    (θ : ℝ) (w : ℤ) (hw : w ≠ 0) (u : Fin (n+1) → UnitVector OSFourSpace) (s : Fin (n+1) → OSFourSpace)
    (σ : Measure OSFourSpace) [SFinite σ] (B : ℝ)
    (hB : ∀ y : OSFourSpace, let g := fun k : OSFourSpace => Real.exp (-(L/(2*((n:ℝ)+1)))*‖k+y‖)
      Integrable g σ ∧ (∫ k, g k ∂σ) ≤ B) :
    let F := fun t : (Fin n → ℝ) × OSFourSpace => normalWindingTrace m L θ w u (fun j => t.2+s j) t.1
    Integrable F (volume.prod σ) ∧ (∫ t, ‖F t‖ ∂volume.prod σ) ≤ normalWindingBudget n m L B * normalWindingRate m L w := by
  let K := L*(4*2^(n+1))*normalWindingRate m L w
  let f := fun x : ℝ => Real.exp (-(m/4)*|x|)
  let g := fun k : OSFourSpace => ∑ j, Real.exp (-(L/(2*((n:ℝ)+1)))*‖k+s j‖)
  let F := fun t : (Fin n → ℝ) × OSFourSpace => normalWindingTrace m L θ w u (fun j => t.2+s j) t.1
  have hm' : 0 < m/2 := by positivity
  have hf := normal_open_laplace_mass hm'
  rw [show m/2/2=m/4 by ring,show 4/(m/2)=8/m by ring] at hf
  have hprod : Integrable (fun x : Fin n → ℝ => ∏ j, f (x j)) := Integrable.fintype_prod (fun _ : Fin n => hf.1)
  have hg : Integrable g σ := integrable_finset_sum _ (fun j _ => (hB (s j)).1)
  have hgb : (∫ k, g k ∂σ) ≤ (n+1:ℕ)*B := by
    dsimp only [g]
    rw [integral_finset_sum _ (fun j _ => (hB (s j)).1)]
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Finset.sum_le_sum
      (s := (Finset.univ : Finset (Fin (n+1)))) (fun j _ => (hB (s j)).2)
  have hi := (hprod.mul_prod hg).const_mul K
  have hmF : Measurable F := normal_winding_trace_measurable m L θ w u
    (fun j => measurable_snd.add_const (s j)) (fun j => (measurable_pi_apply j).comp measurable_fst)
  have hle (t : (Fin n → ℝ) × OSFourSpace) : ‖F t‖ ≤ K*((∏ i, f (t.1 i))*g t.2) := by
    apply (normal_winding_trace_majorant hm hL θ hw u _ _).trans_eq
    simp only [K,g,f,normalWindingRate,mul_assoc]
  have hF := hi.mono' hmF.aestronglyMeasurable (Eventually.of_forall hle)
  refine ⟨hF,(integral_mono hF.norm hi hle).trans ?_⟩
  rw [integral_const_mul,integral_prod_mul (fun x : Fin n → ℝ => ∏ j, f (x j)) g,integral_fintype_prod_volume_eq_pow f]
  rw [show (∫ x, f x) = 8/m from hf.2]
  simp only [Fintype.card_fin]
  have hK : 0 ≤ K*(8/m)^n := by dsimp [K,normalWindingRate]; positivity
  rw [←mul_assoc]
  apply (mul_le_mul_of_nonneg_left hgb hK).trans_eq
  dsimp [K,normalWindingBudget]; ring

theorem normal_volume_exponential_shifts {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : OSFourSpace, let g := fun k : OSFourSpace => Real.exp (-a*‖k+y‖)
      Integrable g ∧ (∫ k, g k) ≤ B := by
  refine ⟨∫ k : OSFourSpace, Real.exp (-a*‖k‖),integral_nonneg (fun _ => (Real.exp_pos _).le),fun y => ?_⟩
  exact ⟨(measurePreserving_add_right volume y).integrable_comp_of_integrable (normal_carrier_exponential ha),
    (integral_add_right_eq_self (fun k => Real.exp (-a*‖k‖)) y).le⟩

/-- Uniform even when the photon transfers depend on the integer winding.
The zero winding is reserved for the separate Fourier argument. -/
theorem normal_nonzero_windings_absolute {m L : ℝ} (hm : 0 < m) (hL : 0 < L) (θ : ℝ)
    (u : Fin (n+1) → UnitVector OSFourSpace) (s : ℤ → Fin (n+1) → OSFourSpace) :
    let F := fun (w : ℤ) (t : (Fin n → ℝ) × OSFourSpace) =>
      normalWindingTrace m L θ w u (fun j => t.2+s w j) t.1
    (∀ w ≠ 0, Integrable (F w)) ∧ Summable (fun w : ℤ => if w = 0 then 0 else ∫ t, ‖F w t‖) := by
  obtain ⟨B,hB,hsh⟩ := normal_volume_exponential_shifts (a := L/(2*((n:ℝ)+1))) (by positivity)
  have hh (w : ℤ) (hw : w ≠ 0) := normal_winding_trace_integral hm hL θ w hw u (s w) volume B hsh
  refine ⟨fun w hw => (hh w hw).1,?_⟩
  apply Summable.of_nonneg_of_le (fun w => by split_ifs <;> first | exact le_rfl | exact integral_nonneg fun _ => norm_nonneg _) _
    ((normal_winding_rate_summable hm hL).mul_left (normalWindingBudget n m L B))
  intro w
  split_ifs with hw
  · dsimp only [normalWindingBudget,normalWindingRate]; positivity
  · exact (hh w hw).2

end UV
