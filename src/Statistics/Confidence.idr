module Statistics.Confidence

import public Data.Functor.TraverseSt

import Data.DPair
import public Data.Nat
import public Data.Vect

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
    z = cast $ invnormcdf $ inv $ confidence / 2
    zz_n = z * z / n

    midpoint = p + zz_n / 2

    offset = z / (1 + zz_n) * sqrt (p * (1 - p) / n + zz_n / (4 * n))

    denominator = 1 + zz_n

    low  = (midpoint - offset) / denominator
    high = (midpoint + offset) / denominator

  in if low == low && high == high
       then mapHom (P . roughlyFit) (low, high)
       else (0, 1) -- we've gone too close to infinite `z`

--- Performing some actions while having statistical significance of coverage test ---

public export
record CoverageTest a where
  constructor Cover
  minimalProbability, maximalProbability : Probability
  {auto 0 minMaxCorrect : So $ minimalProbability <= maximalProbability}
  successCondition : a -> Bool

namespace CoverageTest

  public export %inline
  DefaultTolerance : Probability
  DefaultTolerance = 95.percent

  export
  coverBetween : {default DefaultTolerance tolerance : Probability} ->
                 (minP, maxP : Probability) ->
                 (successCondition : a -> Bool) ->
                 CoverageTest a
  coverBetween minP maxP = do
    let (minP, maxP) = (min minP maxP, max minP maxP)
    let minP = minP * tolerance
    let maxP = inv $ maxP.inv * tolerance
    let maxP = if maxP <= minP then minP else maxP -- just in case `maxP` is a non-normalised very small value
    Cover minP maxP @{believe_me Oh}

  export
  coverMin : {default DefaultTolerance tolerance : Probability} ->
             (minP : Probability) ->
             (successCondition : a -> Bool) ->
             CoverageTest a
  coverMin minP = coverBetween {tolerance} minP 1

  export
  coverWith : {default DefaultTolerance tolerance : Probability} ->
              (singleP : Probability) ->
              (successCondition : a -> Bool) ->
              CoverageTest a
  coverWith singleP = coverBetween {tolerance} singleP singleP

public export
data SignificantBounds
  = BoundsOk
  | UpperBoundViolated Probability
  | LowerBoundViolated Probability

public export
isOk : SignificantBounds -> Bool
isOk BoundsOk = True
isOk _        = False

export
Interpolation SignificantBounds where
  interpolate BoundsOk               = "ok"
  interpolate $ UpperBoundViolated x = "(..., ...) --> \{show x}"
  interpolate $ LowerBoundViolated x = "\{show x} <-- (..., ...)"

-- `Just` means "statistical significance", `Nothing` means "no significance yet".
public export %inline
CoverageTestResult : Type
CoverageTestResult = Maybe SignificantBounds

export
checkCoverageConditions :
  TraversableSt t =>
  {default (1/1000000000) confidence : Probability} ->
  Vect n (CoverageTest a) ->
  t a ->
  t $ Vect n CoverageTestResult

checkCoverageConditions coverageTests = mapSt checkCoverageOnce initialResults where

  data PastResults : Type where
    R : (attempts : Nat) -> (successes : Vect n $ Subset Nat (`LTE` attempts)) -> PastResults

  initialResults : PastResults
  initialResults = R 0 $ coverageTests <&> const (0 `Element` LTEZero)

  checkCoverageOnce : a -> PastResults -> (PastResults, Vect n CoverageTestResult)
  checkCoverageOnce x $ R prevAttempts prevResults = do
    let %inline currAttempts : Nat; currAttempts = S prevAttempts
    mapFst (R currAttempts) $ unzip $ coverageTests `zip` prevResults <&>
      \(Cover minP maxP cond, Element prevSucc _) => do
        let pr@(Element currSucc _) = if cond x
                                       then S prevSucc `Element` LTESucc %search
                                       else prevSucc   `Element` lteSuccRight %search
        let (wLow, wHigh) = wilsonBounds confidence currAttempts $ ratio currSucc currAttempts
        let confRes = if      wLow >= minP && wHigh <= maxP then Just BoundsOk
                      else if wLow > maxP                   then Just $ UpperBoundViolated wLow
                      else if                 wHigh < minP  then Just $ LowerBoundViolated wHigh
                      else                                       Nothing
        (pr, confRes)
