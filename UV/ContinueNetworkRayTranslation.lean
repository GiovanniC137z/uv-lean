import UV.ContinueNetworkCentering
import UV.ContinueNetworkPrecisionDegreeChart

/-! The actual directional ray polynomial after centering has a
translated base point and an unchanged direction. -/

noncomputable section

namespace UV.ContinueNetworkPrecision

theorem rayPolynomial_translate {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (v : DirectionalMomentum d) (x w : Fin d → ℝ) :
    rayPolynomial (translateDirectionalPolynomial v P) x w =
      rayPolynomial P (fun i => x i + v i) w := by
  apply Polynomial.funext
  intro s
  rw [rayPolynomial_eval,rayPolynomial_eval,translate_directional_polynomial_eval]
  apply congrArg (fun z => MvPolynomial.eval z P)
  funext i
  simp only [Complex.ofReal_add]
  ring

theorem rayDegreeSet_translate {d : ℕ} (K : Submodule ℝ (DirectionalMomentum d))
    (P : MvPolynomial (Fin d) ℂ) (v : DirectionalMomentum d) :
    rayDegreeSet K (translateDirectionalPolynomial v P) = rayDegreeSet K P := by
  ext n
  constructor
  · rintro ⟨x,w,hw,hn,hd⟩
    have h := rayPolynomial_translate P v (fun i => x i) (fun i => w i)
    change _ = rayPolynomial P (fun i => (x+v) i) (fun i => w i) at h
    exact ⟨x+v,w,hw,h ▸ hn,h ▸ hd⟩
  · rintro ⟨x,w,hw,hn,hd⟩
    have h := rayPolynomial_translate P v (fun i => (x-v) i) (fun i => w i)
    change _ = rayPolynomial P (fun i => ((x-v)+v) i) (fun i => w i) at h
    rw [sub_add_cancel] at h
    exact ⟨x-v,w,hw,h.symm ▸ hn,h.symm ▸ hd⟩

theorem directionalDegree_translate {d : ℕ} (K : Submodule ℝ (DirectionalMomentum d))
    (P : MvPolynomial (Fin d) ℂ) (v : DirectionalMomentum d) :
    directionalDegree K (translateDirectionalPolynomial v P) = directionalDegree K P := by
  unfold directionalDegree
  rw [rayDegreeSet_translate]

end UV.ContinueNetworkPrecision
