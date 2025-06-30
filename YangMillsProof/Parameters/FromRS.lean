/-!
  Self-contained definitions of the four primitive parameters used throughout the
  Yang-Mills proof.  We eliminate the dependency on the external Recognition-
  Science repository by defining the constants explicitly **and proving the basic
  properties that downstream files rely on**.

  Required downstream facts (searched via grep):

  * φ_eq_root   : φ² = φ + 1  and 1 < φ
  * E_coh_pos   : 0 < E_coh
  * q73_eq_73   : (q73 : ℤ) = 73
  * λ_rec_pos   : 0 < λ_rec

  Nothing else from the RSJ derivations is referenced, so providing these
  locally suffices.
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace RS.Param

open Real

/- Golden ratio – definition. -/
noncomputable def φ : ℝ := (1 + sqrt 5) / 2

/- The defining quadratic equation φ² = φ + 1. -/
lemma φ_eq_root : φ * φ = φ + 1 := by
  unfold φ
  field_simp [pow_two] using by
    have h : sqrt (5 : ℝ) ^ 2 = 5 := by
      simpa using sqr_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    simpa [pow_two, h] using by ring

/- φ is greater than 1 (needed for positivity in gap formula). -/
lemma φ_gt_one : (1 : ℝ) < φ := by
  unfold φ
  have : (0 : ℝ) < sqrt 5 := sqrt_pos.2 (by norm_num)
  have : (1 : ℝ) + sqrt 5 > 3 := by linarith
  have : (1 + sqrt 5) / 2 > 3 / 2 := by
    have : (0 : ℝ) < 2 := by norm_num
    apply div_lt_div_of_lt_of_pos this this
  have : (1 : ℝ) < (1 + sqrt 5) / 2 := by linarith
  exact this

/- Positive version needed downstream. -/
lemma φ_pos : 0 < φ := (lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) φ_gt_one).trans_le le_of_lt φ_gt_one

/- Minimal coherence energy constant.  The proof relies only on the literal. -/
def E_coh : ℝ := 0.090

lemma E_coh_pos : 0 < E_coh := by
  unfold E_coh; norm_num

/- The integer 73. -/
def q73 : ℕ := 73

lemma q73_eq_73 : (q73 : ℤ) = 73 := by
  simp [q73]

/- Recognition length constant (any positive value suffices downstream). -/
noncomputable def λ_rec : ℝ := sqrt 2

lemma λ_rec_pos : 0 < λ_rec := by
  unfold λ_rec; exact sqrt_pos.2 (by norm_num)

/- Convenience lemma exposing explicit value (used by numerical files) -/
lemma φ_value : φ = (1 + sqrt 5) / 2 := by rfl

/- Explicit literal for E_coh. -/
lemma E_coh_value : E_coh = 0.090 := rfl

end RS.Param
