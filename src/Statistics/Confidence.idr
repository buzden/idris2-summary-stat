module Statistics.Confidence

import public Data.Functor.TraverseSt

import Data.DPair
import public Data.Nat
import Data.String
import public Data.Vect

import public Statistics.Norm.Rough
import public Statistics.Probability

-- This module reexports the rough implementation for `InvNormCDF` for compatility reasons, this may be changed in the future

%default total

-- In order to get an accurate measurement with small sample sizes, we're using the Wilson score interval
-- https://en.wikipedia.org/wiki/Binomial_proportion_confidence_interval#Wilson_score_interval
export
wilsonBounds :
  InvNormCDF =>
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

--- Stuff for expressing what and how should be tested ---

public export
record CoverageTest a where
  constructor Cover
  checkedProbability : (Probability, Probability)
  {auto 0 minMaxCorrect : So $ fst checkedProbability <= snd checkedProbability}
  successCondition : a -> Bool

namespace CoverageTest

  public export %inline
  minimalProbability : CoverageTest a -> Probability
  minimalProbability = fst . checkedProbability

  public export %inline
  (.minimalProbability) : CoverageTest a -> Probability
  (.minimalProbability) = minimalProbability

  public export %inline
  maximalProbability : CoverageTest a -> Probability
  maximalProbability = snd . checkedProbability

  public export %inline
  (.maximalProbability) : CoverageTest a -> Probability
  (.maximalProbability) = maximalProbability

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
    Cover (minP, maxP) @{believe_me Oh}

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
DefaultConfidence : Probability
DefaultConfidence = 1/1000000000

--- Coverage condition checker with low-level intermediate results ---

public export
record CoverageTestState where
  constructor MkCoverageTestState
  testedBounds : (Probability, Probability)
  wilsonBounds : (Probability, Probability)

export
[NoAnalysis] Interpolation CoverageTestState where
  interpolate $ MkCoverageTestState (minP, maxP) (wLow, wHigh) = do
    let ss = if minP == maxP && wLow /= minP && wHigh /= maxP
               then [ (wLow , "[\{show wLow}")
                    , (minP , "(\{show minP})")
                    , (wHigh, "\{show wHigh}]")
                    ]
               else [ (minP , "(\{show minP}")
                    , (wLow , "[\{show wLow}")
                    , (wHigh, "\{show wHigh}]")
                    , (maxP , "\{show maxP})")
                    ]
    unwords $ map snd $ sortBy (comparing fst) ss

export
[Means] Interpolation CoverageTestState where
  interpolate $ MkCoverageTestState expected wilson = "expected: \{interpolatePair expected}, wilson: \{interpolatePair wilson}" where
    interpolatePair : (Probability, Probability) -> String
    interpolatePair (lo, hi) = do
      let lo = lo.value
          hi = hi.value
      if lo == hi then "\{show lo}" else with Bounded.(+) with Bounded.(/) with Bounded.(-) do
        let mi = (lo + hi) / 2
        let di = hi - mi
        "\{show mi} ± \{show di}"

export
checkCoverageConditions' :
  TraversableSt t =>
  InvNormCDF =>
  {default DefaultConfidence confidence : Probability} ->
  Vect n (CoverageTest a) ->
  t a ->
  t $ Vect n CoverageTestState

checkCoverageConditions' coverageTests = traverseSt checkCoverageOnce initialResults where

  data PastResults : Type where
    R : (attempts : Nat) -> (successes : Vect n $ Subset Nat (`LTE` attempts)) -> PastResults

  initialResults : PastResults
  initialResults = R 0 $ coverageTests <&> const (0 `Element` LTEZero)

  checkCoverageOnce : a -> PastResults -> (PastResults, Vect n CoverageTestState)
  checkCoverageOnce x $ R prevAttempts prevResults = do
    let %inline currAttempts : Nat; currAttempts = S prevAttempts
    mapFst (R currAttempts) $ unzip $ coverageTests `zip` prevResults <&>
      \(Cover checkedP@(minP, maxP) cond, Element prevSucc _) => do
        let pr@(Element currSucc _) = if cond x
                                        then S prevSucc `Element` LTESucc %search
                                        else prevSucc   `Element` lteSuccRight %search
        (pr, MkCoverageTestState checkedP $ wilsonBounds confidence currAttempts $ ratio currSucc currAttempts)

--- Coverage condition checkers with simpler results ---

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
coverageTestResult : CoverageTestState -> CoverageTestResult
coverageTestResult $ MkCoverageTestState (minP, maxP) (wLow, wHigh) =
  if      wLow >= minP && wHigh <= maxP then Just BoundsOk
  else if wLow > maxP                   then Just $ UpperBoundViolated wLow
  else if                 wHigh < minP  then Just $ LowerBoundViolated wHigh
  else                                       Nothing

export
Interpolation CoverageTestState where
  interpolate cts@(MkCoverageTestState (minP, maxP) (wLow, wHigh)) = case coverageTestResult cts of
    Just BoundsOk               => "ok"
    Just (UpperBoundViolated _) => "(..., \{show maxP}) --> \{show wLow}"
    Just (LowerBoundViolated _) => "\{show wLow} <-- (\{show minP}, ...)"
    Nothing                     => "\{show wLow} .. \{show wHigh} still covers (\{show minP}, \{show maxP})"

export %inline
checkCoverageConditions :
  TraversableSt t =>
  InvNormCDF =>
  {default DefaultConfidence confidence : Probability} ->
  Vect n (CoverageTest a) ->
  t a ->
  t $ Vect n CoverageTestResult
checkCoverageConditions = map @{FromTraversableSt} (map coverageTestResult) .: checkCoverageConditions' {confidence}

export %inline
checkCoverageCondition :
  TraversableSt t =>
  InvNormCDF =>
  {default DefaultConfidence confidence : Probability} ->
  CoverageTest a ->
  t a ->
  t CoverageTestResult
checkCoverageCondition ct = map @{FromTraversableSt} head . checkCoverageConditions {confidence} [ct]
