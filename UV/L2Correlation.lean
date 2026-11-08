import UV.CliffordWard
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! Actual L² correlations on four-dimensional Euclidean momentum space.
The translate is continuous in L²; its scalar product with a fixed L²
function identifies the literal absolutely convergent loop integral. -/

noncomputable section
open MeasureTheory
open scoped Topology ENNReal InnerProductSpace ComplexConjugate

namespace UV

theorem memLp_two_mul_translate_integrable {f g : DiracMomentum → ℂ}
    (hf : MemLp f 2) (hg : MemLp g 2) (Q : DiracMomentum) :
    Integrable (fun k => f k * g (k + Q)) := by
  exact hf.integrable_mul (hg.comp_measurePreserving (measurePreserving_add_right volume Q))

theorem memLp_two_correlation_continuous {f g : DiracMomentum → ℂ}
    (hf : MemLp f 2) (hg : MemLp g 2) :
    Continuous (fun Q : DiracMomentum => ∫ k, f k * g (k + Q)) := by
  let T : DiracMomentum → C(DiracMomentum, DiracMomentum) :=
    fun Q => ⟨fun k => k + Q, continuous_id.add continuous_const⟩
  have hT : Continuous T := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_snd.add continuous_fst
  have hMP (Q : DiracMomentum) : MeasurePreserving (T Q) volume volume :=
    measurePreserving_add_right volume Q
  have hshift : Continuous (fun Q : DiracMomentum =>
      Lp.compMeasurePreserving (T Q) (hMP Q) (hg.toLp g)) :=
    continuous_const.compMeasurePreservingLp hT hMP (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have hcor : Continuous (fun Q : DiracMomentum =>
      ⟪hf.star.toLp (star f), Lp.compMeasurePreserving (T Q) (hMP Q) (hg.toLp g)⟫_ℂ) :=
    continuous_const.inner hshift
  apply hcor.congr
  intro Q
  rw [L2.inner_def]
  apply integral_congr_ae
  have hshiftAE : Lp.compMeasurePreserving (T Q) (hMP Q) (hg.toLp g) =ᵐ[volume]
      (fun k => g (k + Q)) :=
    (Lp.coeFn_compMeasurePreserving _ (hMP Q)).trans ((hMP Q).quasiMeasurePreserving.ae hg.coeFn_toLp)
  filter_upwards [hf.star.coeFn_toLp, hshiftAE] with k hfk hgk
  rw [hfk, hgk, RCLike.inner_apply']
  simp

end UV
