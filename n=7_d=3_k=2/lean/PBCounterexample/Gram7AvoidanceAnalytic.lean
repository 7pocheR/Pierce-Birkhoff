import PBCounterexample.Gram7Implicit
import PBCounterexample.FiniteJet

/-! Polynomial evaluation of the real implicit chart and its approximations. -/

noncomputable section

namespace PBCounterexample.Gram7

open Filter Asymptotics
open scoped Topology

def polynomialAlongApproximation (a : Fin 7 → Polynomial ℝ)
    (p : MvPolynomial (Fin 7) ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C a p

theorem polynomialAlongApproximation_eval (a : Fin 7 → Polynomial ℝ)
    (p : MvPolynomial (Fin 7) ℝ) (t : ℝ) :
    (polynomialAlongApproximation a p).eval t =
      MvPolynomial.eval (fun i => (a i).eval t) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [polynomialAlongApproximation]
  | add p q hp hq =>
    simpa only [polynomialAlongApproximation, MvPolynomial.eval₂_add,
      Polynomial.eval_add, map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
    simpa only [polynomialAlongApproximation, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X, Polynomial.eval_mul, map_mul, MvPolynomial.eval_X]
      using congrArg (fun x => x * (a i).eval t) hp

theorem polynomial_eval_contDiff (p : MvPolynomial (Fin 7) ℝ) :
    ContDiff ℝ 1 (fun z : Coord => MvPolynomial.eval z p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : Coord => r))
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    have hi : ContDiff ℝ 1 (fun z : Coord => z i) := by fun_prop
    simpa using hp.mul hi

theorem coordinates_chart_contDiff :
    ContDiff ℝ 1 (fun p : ChartParameter => coordinates (chart p)) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_pi.mp (chart_contDiff.of_le (by simp))) (negativeIndex i)

theorem polynomial_chart_contDiff (p : MvPolynomial (Fin 7) ℝ) :
    ContDiff ℝ 1 (fun z : ChartParameter =>
      MvPolynomial.eval (coordinates (chart z)) p) :=
  (polynomial_eval_contDiff p).comp coordinates_chart_contDiff

theorem polynomial_chart_approximation_error_isBigO
    (a : Fin 7 → Polynomial ℝ)
    (hbase : (fun i => (a i).eval 0) = chartBase)
    (N : ℕ)
    (hres : (fun t => chartSystem (t, fun i => (a i).eval t)) =O[𝓝 0]
      (fun t : ℝ => t^N))
    (p : MvPolynomial (Fin 7) ℝ) :
    (fun t => MvPolynomial.eval (baseCurve t) p -
      MvPolynomial.eval (coordinates (chart (t, fun i => (a i).eval t))) p)
      =O[𝓝 0] (fun t : ℝ => t^N) := by
  have ha : Tendsto (fun t => fun i => (a i).eval t) (𝓝 0) (𝓝 chartBase) := by
    have hc := (continuous_pi (fun i => (a i).continuous)).tendsto 0
    simpa only [hbase] using hc
  have he := chartFunctionApproximation_error_isBigO
    (fun z : ChartParameter => MvPolynomial.eval (coordinates (chart z)) p)
    (polynomial_chart_contDiff p).contDiffAt ha hres
  simpa only [baseCurve, implicitChart, neg_sub] using he.neg_left

end PBCounterexample.Gram7
