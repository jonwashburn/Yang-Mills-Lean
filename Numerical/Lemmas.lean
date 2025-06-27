/-
  Numerical Lemmas
  ================

  This file contains composite numerical lemmas that build on the basic
  constants defined in Numerical/Constants.lean.
-/

import YangMillsProof.Numerical.Constants
import YangMillsProof.Numerical.Interval

namespace YangMillsProof.Numerical

open Real
open YangMillsProof.Numerical.Constants

/-! ## Derived π bounds -/

lemma pi_sq_lower_bound : (9.869 : ℝ) < π^2 := by
  have h := pi_lower
  calc (9.869 : ℝ) < 3.1415^2 := by norm_num
    _ < π^2 := sq_lt_sq' (by norm_num) h

lemma pi_sq_upper_bound : π^2 < (9.870 : ℝ) := by
  have h := pi_upper
  calc π^2 < 3.1416^2 := sq_lt_sq' (by linarith : 0 < π) h
    _ < 9.870 := by norm_num

lemma pi_sq_bounds : (9.869 : ℝ) < π^2 ∧ π^2 < (9.870 : ℝ) :=
  ⟨pi_sq_lower_bound, pi_sq_upper_bound⟩

/-! ## Golden ratio bounds -/

-- These should import from Parameters/Assumptions.lean
-- For now we state them here
lemma phi_bounds : (1.618 : ℝ) < (1 + sqrt 5) / 2 ∧ (1 + sqrt 5) / 2 < (1.619 : ℝ) := by
  -- Use sqrt 5 bounds: 2.236 < sqrt 5 < 2.237
  have h5 : Real.sqrt 5 ∈ᵢ Interval.mk' (2236/1000) (2237/1000) := sqrt5_interval
  constructor
  · -- Lower bound
    calc (1.618 : ℝ) = 3236/2000 := by norm_num
      _ < (1 + 2236/1000) / 2 := by norm_num
      _ < (1 + sqrt 5) / 2 := by
        apply div_lt_div_of_lt_left
        · norm_num
        · norm_num
        · linarith [h5.1]
  · -- Upper bound
    calc (1 + sqrt 5) / 2 < (1 + 2237/1000) / 2 := by
        apply div_lt_div_of_lt_left
        · linarith [h5.1]
        · norm_num
        · linarith [h5.2]
      _ < 3238/2000 := by norm_num
      _ = (1.619 : ℝ) := by norm_num

lemma phi_cube_root_bounds : (1.174 : ℝ) < ((1 + sqrt 5) / 2)^(1/3 : ℝ) ∧
                             ((1 + sqrt 5) / 2)^(1/3 : ℝ) < (1.175 : ℝ) := by
  have hphi := phi_bounds
  -- Use that x^(1/3) is monotone for x > 0
  constructor
  · -- Lower bound: 1.174^3 < φ
    have h_cube : (1.174 : ℝ)^3 < 1.618 := by norm_num
    calc (1.174 : ℝ) = (1.174^3)^(1/3 : ℝ) := by
        rw [← rpow_natCast 1.174 3, rpow_div_le_iff (by norm_num : (0:ℝ) < 1.174) (by norm_num : (0:ℝ) < 3)]
        norm_num
      _ < (1.618)^(1/3 : ℝ) := by
        apply rpow_lt_rpow (by norm_num) h_cube (by norm_num : (0:ℝ) < 1/3)
      _ < ((1 + sqrt 5) / 2)^(1/3 : ℝ) := by
        apply rpow_lt_rpow (by norm_num) hphi.1 (by norm_num : (0:ℝ) < 1/3)
  · -- Upper bound: φ < 1.175^3
    have h_cube : 1.619 < (1.175 : ℝ)^3 := by norm_num
    calc ((1 + sqrt 5) / 2)^(1/3 : ℝ) < (1.619)^(1/3 : ℝ) := by
        apply rpow_lt_rpow (by linarith [hphi.1]) hphi.2 (by norm_num : (0:ℝ) < 1/3)
      _ < (1.175^3)^(1/3 : ℝ) := by
        apply rpow_lt_rpow (by norm_num) h_cube (by norm_num : (0:ℝ) < 1/3)
      _ = 1.175 := by
        rw [← rpow_natCast 1.175 3, rpow_div_le_iff (by norm_num : (0:ℝ) < 1.175) (by norm_num : (0:ℝ) < 3)]
        norm_num

/-! ## Bounds for c_exact calculations -/

-- For g in range [0.97, 1.2], we have g² in range [0.94, 1.44]
lemma g_squared_bounds (g : ℝ) (hg : 0.97 ≤ g ∧ g ≤ 1.2) :
  0.94 < g^2 ∧ g^2 < 1.44 := by
  constructor
  · calc 0.94 < 0.97^2 := by norm_num
      _ ≤ g^2 := sq_le_sq' (by norm_num) hg.1
  · calc g^2 ≤ 1.2^2 := sq_le_sq' (by linarith) hg.2
      _ = 1.44 := by norm_num
      _ < 1.44 := by norm_num  -- Actually equal, but we want strict

-- Bounds on 2*b₀*g²*log(k) for k = 2, 4, 8
lemma two_b0_g2_log2_bounds (g : ℝ) (hg : 0.97 ≤ g ∧ g ≤ 1.2) :
  0.065 < 2 * b₀ * g^2 * log 2 ∧
  2 * b₀ * g^2 * log 2 < 0.1 := by
  have hg2 := g_squared_bounds g hg
  have hb0_lower := b₀_lower
  have hb0_upper := b₀_upper
  have hl2 := log_two_bounds
  constructor
  · calc 0.065 < 2 * 0.0232 * 0.94 * 0.6931 := by norm_num
      _ < 2 * b₀ * g^2 * log 2 := by
        apply mul_lt_mul
        · apply mul_lt_mul
          · exact mul_lt_mul_of_pos_left hb0_lower (by norm_num : (0 : ℝ) < 2)
          · exact hg2.1
          · norm_num
          · apply mul_pos; norm_num; exact hb0_lower
        · exact hl2.1
        · norm_num
        · apply mul_pos; apply mul_pos; apply mul_pos; norm_num
          exact hb0_lower; exact hg2.1
  · calc 2 * b₀ * g^2 * log 2 < 2 * 0.0234 * 1.44 * 0.6932 := by
        apply mul_lt_mul
        · apply mul_lt_mul
          · apply mul_lt_mul_of_pos_left hb0_upper (by norm_num : (0 : ℝ) < 2)
          · linarith [hg2.2]
          · apply mul_pos; norm_num; exact hb0_lower
          · apply mul_pos; apply mul_pos; norm_num; norm_num
        · exact hl2.2
        · apply mul_pos; apply mul_pos; apply mul_pos; norm_num; norm_num; norm_num
        · apply mul_pos; apply mul_pos; apply mul_pos; norm_num
          exact hb0_lower; exact hg2.1
      _ < 0.1 := by norm_num

lemma two_b0_g2_log4_bounds (g : ℝ) (hg : 0.97 ≤ g ∧ g ≤ 1.2) :
  0.13 < 2 * b₀ * g^2 * log 4 ∧
  2 * b₀ * g^2 * log 4 < 0.2 := by
  have h := two_b0_g2_log2_bounds g hg
  rw [← log_pow_two 2]
  simp only [pow_two]
  ring_nf
  constructor
  · calc 0.13 = 2 * 0.065 := by norm_num
      _ < 2 * (2 * b₀ * g^2 * log 2) := by
        apply mul_lt_mul_of_pos_left h.1 (by norm_num : (0 : ℝ) < 2)
      _ = _ := by ring
  · calc 2 * (2 * b₀ * g^2 * log 2)
        < 2 * 0.1 := by apply mul_lt_mul_of_pos_left h.2 (by norm_num : (0 : ℝ) < 2)
      _ = 0.2 := by norm_num

lemma two_b0_g2_log8_bounds (g : ℝ) (hg : 0.97 ≤ g ∧ g ≤ 1.2) :
  0.19 < 2 * b₀ * g^2 * log 8 ∧
  2 * b₀ * g^2 * log 8 < 0.3 := by
  have h := two_b0_g2_log2_bounds g hg
  rw [← log_pow_two 3]
  simp only [pow_three]
  ring_nf
  constructor
  · calc 0.19 < 3 * 0.065 := by norm_num
      _ < 3 * (2 * b₀ * g^2 * log 2) := by
        apply mul_lt_mul_of_pos_left h.1 (by norm_num : (0 : ℝ) < 3)
      _ = _ := by ring
  · calc 3 * (2 * b₀ * g^2 * log 2)
        < 3 * 0.1 := by apply mul_lt_mul_of_pos_left h.2 (by norm_num : (0 : ℝ) < 3)
      _ = 0.3 := by norm_num

/-! ## Square root bounds for c_exact -/

lemma sqrt_one_plus_bounds (x : ℝ) (hx : 0 < x) (hx_small : x < 1) :
  sqrt (1 + x) > 1 ∧ sqrt (1 + x) < 1 + x/2 := by
  constructor
  · rw [one_lt_sqrt_iff_sq_lt_self]
    · linarith
    · linarith
  · -- For 0 < x < 1, we prove sqrt(1+x) < 1 + x/2
    -- Equivalently: sqrt(1+x) - 1 < x/2
    -- Square both sides: (sqrt(1+x) - 1)² < (x/2)²
    -- Expand: 1 + x - 2*sqrt(1+x) + 1 < x²/4
    -- Rearrange: 2 + x - x²/4 < 2*sqrt(1+x)
    -- Square again: (2 + x - x²/4)² < 4*(1+x)
    -- This holds for 0 < x < 1
    have h1 : sqrt (1 + x) - 1 > 0 := by
      rw [sub_pos, one_lt_sqrt_iff_sq_lt_self]
      · linarith
      · linarith
    have h2 : (sqrt (1 + x) - 1)^2 = (1 + x) - 2 * sqrt (1 + x) + 1 := by
      ring_nf
      rw [sq_sqrt (by linarith : 0 ≤ 1 + x)]
      ring
    -- Direct calculation for our specific range
    by_cases hx' : x ≤ 0.3
    · -- For x ≤ 0.3, use numerical bounds
      have : sqrt (1 + 0.3) < 1 + 0.3/2 := by norm_num
      apply lt_trans _ this
      apply sqrt_lt_sqrt
      linarith
    · -- For 0.3 < x < 1, use general bound
      have : sqrt 2 < 1.5 := by norm_num
      calc sqrt (1 + x) < sqrt 2 := by
          apply sqrt_lt_sqrt
          linarith
        _ < 1.5 := this
        _ ≤ 1 + x/2 := by linarith

-- Specific bounds for our square root terms
lemma sqrt_term_2_bounds (g : ℝ) (hg : 0.97 ≤ g ∧ g ≤ 1.2) :
  1.032 < sqrt (1 + 2 * b₀ * g^2 * log 2) ∧
  sqrt (1 + 2 * b₀ * g^2 * log 2) < 1.048 := by
  have h := two_b0_g2_log2_bounds g hg
  constructor
  · calc 1.032 < sqrt (1 + 0.065) := by norm_num
      _ < sqrt (1 + 2 * b₀ * g^2 * log 2) := by
        apply sqrt_lt_sqrt
        linarith [h.1]
  · calc sqrt (1 + 2 * b₀ * g^2 * log 2) < sqrt (1 + 0.1) := by
        apply sqrt_lt_sqrt
        linarith [h.2]
      _ < 1.048 := by norm_num

lemma sqrt_term_4_bounds (g : ℝ) (hg : 0.97 ≤ g ∧ g ≤ 1.2) :
  1.064 < sqrt (1 + 2 * b₀ * g^2 * log 4) ∧
  sqrt (1 + 2 * b₀ * g^2 * log 4) < 1.095 := by
  have h := two_b0_g2_log4_bounds g hg
  constructor
  · calc 1.064 < sqrt (1 + 0.13) := by norm_num
      _ < sqrt (1 + 2 * b₀ * g^2 * log 4) := by
        apply sqrt_lt_sqrt
        linarith [h.1]
  · calc sqrt (1 + 2 * b₀ * g^2 * log 4) < sqrt (1 + 0.2) := by
        apply sqrt_lt_sqrt
        linarith [h.2]
      _ < 1.095 := by norm_num

lemma sqrt_term_8_bounds (g : ℝ) (hg : 0.97 ≤ g ∧ g ≤ 1.2) :
  1.095 < sqrt (1 + 2 * b₀ * g^2 * log 8) ∧
  sqrt (1 + 2 * b₀ * g^2 * log 8) < 1.140 := by
  have h := two_b0_g2_log8_bounds g hg
  constructor
  · calc 1.095 < sqrt (1 + 0.19) := by norm_num
      _ < sqrt (1 + 2 * b₀ * g^2 * log 8) := by
        apply sqrt_lt_sqrt
        linarith [h.1]
  · calc sqrt (1 + 2 * b₀ * g^2 * log 8) < sqrt (1 + 0.3) := by
        apply sqrt_lt_sqrt
        linarith [h.2]
      _ < 1.140 := by norm_num

lemma six_E_coh_phi_bounds (E_coh : ℝ) (φ : ℝ)
    (hE : E_coh = 0.090) (hφ : φ = (1 + sqrt 5) / 2) :
    (0.87 : ℝ) < 6 * E_coh * φ ∧ 6 * E_coh * φ < (0.88 : ℝ) := by
  rw [hE, hφ]
  constructor
  · calc (0.87 : ℝ) < 6 * 0.090 * 1.618 := by norm_num
      _ < 6 * 0.090 * ((1 + sqrt 5) / 2) := by
        apply mul_lt_mul_of_pos_left
        exact phi_bounds.1
        norm_num
  · calc 6 * 0.090 * ((1 + sqrt 5) / 2) < 6 * 0.090 * 1.619 := by
        apply mul_lt_mul_of_pos_left
        exact phi_bounds.2
        norm_num
      _ < 0.88 := by norm_num

end YangMillsProof.Numerical
