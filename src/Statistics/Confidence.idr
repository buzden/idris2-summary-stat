module Statistics.Confidence

import public Data.Nat

import Statistics.Erf
import public Statistics.Probability

%default total

-- In order to get an accurate measurement with small sample sizes, we're using the Wilson score interval
-- https://en.wikipedia.org/wiki/Binomial_proportion_confidence_interval#Wilson_score_interval
export
wilsonBounds :
  (confidence : Probability) ->
  (count : Nat) ->
  (0 _ : IsSucc count) =>
  (successes : Probability) ->
  (Probability, Probability)
wilsonBounds confidence count successes =
  let
    n = cast count
    p = successes.asDouble
    z = invnormcdf $ inv $ confidence / 2
    zz_n = z * z / n

    midpoint = p + zz_n / 2

    offset = z / (1 + zz_n) * sqrt (p * (1 - p) / n + zz_n / (4 * n))

    denominator = 1 + zz_n

    low  = (midpoint - offset) / denominator
    high = (midpoint + offset) / denominator

  in mapHom (\x => fromDouble x @{believe_me Oh}) (low, high)
