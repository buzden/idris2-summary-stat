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

  in mapHom (\x => fromDouble x @{believe_me Oh}) (low, high)

--- Performing some actions while having statistical significance of coverage test ---

public export
record CoverageTest a where
  constructor Cover
  successCondition : a -> Bool
  minimalProbability, maximalProbability : Probability
  {auto 0 minMaxCorrect : So $ minimalProbability <= maximalProbability}

public export
data CoverageTestResult
  = SignificantlyTrue
  | SignificantlyFalse
  | NoSignificance

public export
Eq CoverageTestResult where
  SignificantlyTrue  == SignificantlyTrue  = True
  SignificantlyFalse == SignificantlyFalse = True
  NoSignificance     == NoSignificance     = True
  _ == _ = False

-- TODO to add tolerance parameter for required probabilities?
export
checkCoverageConditions :
  TraversableSt t =>
  {default (1/1000000000) confidence : Probability} ->
  {n : _} ->
  Vect n (CoverageTest a) ->
  t a ->
  t $ Vect n CoverageTestResult

checkCoverageConditions coverageTests = mapSt checkCoverageOnce initialResults where

  data PastResults : Type where
    R : (attempts : Nat) -> (successes : Vect n $ Subset Nat (`LTE` attempts)) -> PastResults

  initialResults : PastResults
  initialResults = R 0 $ replicate _ $ 0 `Element` LTEZero

  checkCoverageOnce : a -> PastResults -> (PastResults, Vect n CoverageTestResult)
  checkCoverageOnce x $ R prevAttempts prevResults = do
    let %inline currAttempts : Nat; currAttempts = S prevAttempts
    mapFst (R currAttempts) $ unzip $ coverageTests `zip` prevResults <&>
      \(Cover cond minP maxP, Element prevSucc _) => do
        let pr@(Element currSucc _) = if cond x
                                       then S prevSucc `Element` LTESucc %search
                                       else prevSucc   `Element` lteSuccRight %search
        let (wLow, wHigh) = wilsonBounds confidence currAttempts $ ratio currSucc currAttempts
        let confRes = if      wLow >= minP && wHigh <= maxP then SignificantlyTrue
                      else if wLow > maxP  || wHigh < minP  then SignificantlyFalse
                      else                                       NoSignificance
        (pr, confRes)
