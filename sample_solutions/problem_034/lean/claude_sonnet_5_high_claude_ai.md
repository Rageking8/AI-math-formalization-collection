# Claude Sonnet 5 High (Claude AI)

Model: `Claude Sonnet 5 High` (via Claude AI)\
Date: `8 September 2026`\
Line count: `33`\
Turn count: `1`

## Solution

```lean4
import Mathlib

theorem polynomial_pos_3x8_2x4 (x y : ℝ) :
    3 * x ^ 8 + 2 * x ^ 4 * y ^ 4 - 7 * x ^ 2 * y ^ 2 + 2 * y ^ 6 + 5 / 3 > 0 := by
  have key : 3 * x ^ 8 + 2 * x ^ 4 * y ^ 4 - 7 * x ^ 2 * y ^ 2 + 2 * y ^ 6 + 5 / 3 =
      1 / 20 +
      (97 / 60) * (1 - (144/485) * x^4 - (366/485) * x^2*y^2 - (144/485) * x^2 - (168/485) * y^2)^2 +
      (19473 / 12125) * (y^2 - (16157/38946) * x^4 - (6853/38946) * x^2*y^2 - (26827/38946) * x^2)^2 +
      (1587943 / 1947300) * (x^2 - (2066977/1587943) * x^4 - (266561/1587943) * x^2*y^2)^2 +
      (7992396 / 7939715) * (x^2*y^2 - (9506897/8880440) * x^4)^2 +
      (20311313 / 444022000) * (x^4)^2 +
      (28 / 25) * (y - (4/7) * x^2*y - (45/56) * y^3)^2 +
      (143 / 112) * (y^3 - (3904/3575) * x^2*y)^2 +
      (2832 / 89375) * (x^2*y)^2 +
      (24 / 25) * (x - (19/48) * x^3 - (15/16) * x*y^2)^2 +
      (509 / 800) * (x*y^2 - (541/509) * x^3)^2 +
      (388 / 7635) * (x^3)^2 +
      (2 / 5) * (x*y - (7/5) * x^3*y)^2 +
      (7 / 125) * (x^3*y)^2 := by ring
  have h1 : (0:ℝ) ≤ (97 / 60) * (1 - (144/485) * x^4 - (366/485) * x^2*y^2 - (144/485) * x^2 - (168/485) * y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : (0:ℝ) ≤ (19473 / 12125) * (y^2 - (16157/38946) * x^4 - (6853/38946) * x^2*y^2 - (26827/38946) * x^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : (0:ℝ) ≤ (1587943 / 1947300) * (x^2 - (2066977/1587943) * x^4 - (266561/1587943) * x^2*y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : (0:ℝ) ≤ (7992396 / 7939715) * (x^2*y^2 - (9506897/8880440) * x^4)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h5 : (0:ℝ) ≤ (20311313 / 444022000) * (x^4)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h6 : (0:ℝ) ≤ (28 / 25) * (y - (4/7) * x^2*y - (45/56) * y^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h7 : (0:ℝ) ≤ (143 / 112) * (y^3 - (3904/3575) * x^2*y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h8 : (0:ℝ) ≤ (2832 / 89375) * (x^2*y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h9 : (0:ℝ) ≤ (24 / 25) * (x - (19/48) * x^3 - (15/16) * x*y^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h10 : (0:ℝ) ≤ (509 / 800) * (x*y^2 - (541/509) * x^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h11 : (0:ℝ) ≤ (388 / 7635) * (x^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h12 : (0:ℝ) ≤ (2 / 5) * (x*y - (7/5) * x^3*y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h13 : (0:ℝ) ≤ (7 / 125) * (x^3*y)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  linarith [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13]
```
