import UV.ContinueWilsonSpinExpansion

/-! The return formula with all intermediate spin indices summed. The
ordered trace of a nonempty word of marked momentum-space Wilson hops
equals the relative-displacement integral of its closed polygon spin
trace and its marked phases. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Real
open scoped BigOperators Matrix.Norms.L2Operator

namespace UV

variable {ι : Type*} [Fintype ι] {n : ℕ}

def wilsonMarkedReturn (L : ℝ) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (m : Fin (n+1) → WilsonDirections) (q : Fin (n+1) → OSFourSpace) (d : Fin n → OSFourSpace) : ℂ :=
  wilsonReturnWeight L T d * ∏ k, thinPlaneWave (q k) (wilsonReturnSteps d k) * wilsonDirectionWeight (m k) (wilsonReturnSteps d k)

private theorem wilson_integral_spin_sum {Z K S : Type*} [MeasurableSpace Z] [Fintype K] [Fintype S]
    (μ : Measure Z) (F : K → S → Z → ℂ) (h : ∀ i s, Integrable (F i s) μ) :
    (∫ z, ∑ i, ∑ s, F i s z ∂μ) = ∑ i, ∑ s, ∫ z, F i s z ∂μ := by
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun s _ => h i s))]
  simp_rw [integral_finset_sum _ (fun s _ => h _ s)]

/-- The phase at the distinguished closing step and all other straight
steps enter with the Fourier sign used by the charged source. -/
theorem wilson_closed_spin_trace_return {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (m : Fin (n+1) → WilsonDirections) (q : Fin (n+1) → OSFourSpace) :
    (((2*π)^4)⁻¹ : ℝ) • (∫ p, (List.ofFn (fun k => wilsonSpinHopMatrix L T (m k) (p+q k))).prod.trace) =
      ∫ d, wilsonMarkedReturn L T m q d ∂Measure.pi (fun _ : Fin n => wilsonDisplacementMeasure L T) := by
  let e := fun (i : Fin 4) (s : Fin n → Fin 4) (k : Fin (n+1)) =>
    WilsonSpinEntry.mk (m k) (Fin.cons (α := fun _ => Fin 4) i s k) (Fin.snoc (α := fun _ => Fin 4) s i k)
  let F := fun i s p => (e i s 0).hop L T (p+q 0) * ∏ j : Fin n, (e i s j.succ).hop L T (p+q j.succ)
  let G := fun i s (d : Fin n → OSFourSpace) => (thinPlaneWave (q 0) (-(∑ j, d j)) *
    (e i s 0).density L T (-(∑ j, d j))) * wilsonTailEntryWeight L (fun j : Fin n => e i s j.succ) (fun j => q j.succ) d
  have hF (i s) : Integrable (F i s) := wilson_spin_path_momentum_integrable hL T _ _ _ _
  have hG (i s) : Integrable (G i s) (Measure.pi (fun _ : Fin n => wilsonDisplacementMeasure L T)) :=
    wilson_spin_path_return_integrable hL T _ _ _ _
  have H (i s) : (((2*π)^4)⁻¹ : ℝ) • (∫ p, F i s p) =
      ∫ d, G i s d ∂Measure.pi (fun _ : Fin n => wilsonDisplacementMeasure L T) :=
    wilson_spin_entry_polygon_closure hL T _ _ _ _
  have hleft (p : OSFourSpace) : (List.ofFn (fun k => wilsonSpinHopMatrix L T (m k) (p+q k))).prod.trace =
      ∑ i, ∑ s, F i s p := by
    simp only [wilson_spin_trace_expand,wilsonSpinPath,wilson_spin_hop_entry hL T]
    apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
    exact Fin.prod_univ_succ _
  have hright (d : Fin n → OSFourSpace) : wilsonMarkedReturn L T m q d = ∑ i, ∑ s, G i s d := by
    let A := fun k => wilsonSpinWeight L (wilsonReturnSteps d k)
    let P := fun k => thinPlaneWave (q k) (wilsonReturnSteps d k) * wilsonDirectionWeight (m k) (wilsonReturnSteps d k)
    let h := (wilsonContinuousDensity L T (-(∑ j, d j)) : ℂ)
    change (h * (List.ofFn A).prod.trace) * (∏ k, P k) = _
    rw [wilson_spin_trace_expand,mul_comm (h * _),←mul_assoc,Finset.mul_sum]
    apply Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl fun s _ => ?_
    unfold wilsonSpinPath
    rw [mul_right_comm _ h,←Finset.prod_mul_distrib,Fin.prod_univ_succ]
    simp only [G,wilsonTailEntryWeight,WilsonSpinEntry.amplitude,WilsonSpinEntry.density,wilsonMarkedEntryDensity,e,
      P,A,h,wilsonReturnSteps,Fin.cons_zero,Fin.cons_succ]
    have hprod : (∏ j : Fin n, (thinPlaneWave (q j.succ) (d j) * wilsonDirectionWeight (m j.succ) (d j)) *
        wilsonSpinWeight L (d j) (s j) (Fin.snoc (α := fun _ => Fin 4) s i j.succ)) =
        ∏ j : Fin n, thinPlaneWave (q j.succ) (d j) * (wilsonDirectionWeight (m j.succ) (d j) *
          wilsonSpinWeight L (d j) (s j) (Fin.snoc (α := fun _ => Fin 4) s i j.succ)) := by simp only [mul_assoc]
    rw [hprod]
    ring
  simp_rw [hleft,hright]
  rw [wilson_integral_spin_sum _ F hF,wilson_integral_spin_sum _ G hG,Finset.smul_sum]
  apply Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun s _ => H i s)

/-- The same identity for the ordered matrix word used to define the
charged circulation in the graph bound. -/
theorem wilson_circulation_word_polygon {L : ℝ} (hL : 0 < L) (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι)
    (hs : Fin (n+1) → WilsonCirculationHop) :
    (((2*π)^4)⁻¹ : ℝ) • (∫ p, (wilsonCirculationWord L T (List.ofFn hs) p).trace) =
      ∫ d, wilsonMarkedReturn L T (fun j => (hs j).marks) (fun j => (hs j).transfer) d
        ∂Measure.pi (fun _ : Fin n => wilsonDisplacementMeasure L T) := by
  have he (p : OSFourSpace) (l : List WilsonCirculationHop) : wilsonCirculationWord L T l p =
      (l.map (fun h => wilsonSpinHopMatrix L T h.marks (p+h.transfer))).prod := by
    induction l with
    | nil => rfl
    | cons h l ih => simp only [wilsonCirculationWord,ih,List.map_cons,List.prod_cons]
  simp_rw [he,List.map_ofFn,Function.comp_def]
  exact wilson_closed_spin_trace_return hL T _ _

end UV
