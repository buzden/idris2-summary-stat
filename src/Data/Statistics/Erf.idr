module Data.Statistics.Erf

import Data.Statistics.Probability

import Data.DPair

%default total

--- Algebra on bounded doubles ---

namespace BoundedDoubles

  export
  (/) : Subset Double (\x => So $ lb <= x && x <= ub) -> (y : Double) -> (0 _ : So $ y > 0) => Subset Double $ \x => So $ lb / y <= x && x <= ub / y
  Element x _ / y = Element (x / y) $ believe_me Oh

--- Error function and co ---

%foreign "C:erf, libm 6"
prim_erf : Double -> Double

%foreign "C:erfc, libm 6"
prim_erfc : Double -> Double

export
erf : Double -> Subset Double $ \y => So $ -1 <= y && y <= 1
erf x = prim_erf x `Element` believe_me Oh

export
erfc : Double -> Subset Double $ \y => So $ 0 <= y && y <= 2
erfc x = prim_erfc x `Element` believe_me Oh

-- Code below is based on taken from
-- https://hackage.haskell.org/package/erf-2.0.0.0/docs/src/Data-Number-Erf.html
-- Licensed with BSD-3-Clause, copyright Lennart Augustsson

export
normcdf : Double -> Probability
normcdf x =
  let Element x p = erfc (-x / sqrt 2) / 2
  in P x @{p} -- @{believe_me Oh {- goes from subset bounds -}}

inorm : Probability -> Double
inorm p =
    if      p == 0       then -1/0
    else if p == 1       then 1/0
    else if p < pLow     then closeToLowBound p.asDouble
    else if p.inv < pLow then - closeToLowBound p.inv.asDouble
    else                      middling p.asDouble

  where
    pLow : Probability
    pLow = 0.02425

    closeToLowBound : (p : Double) -> Double
    closeToLowBound p = let
      c1 = -7.784894002430293e-03
      c2 = -3.223964580411365e-01
      c3 = -2.400758277161838e+00
      c4 = -2.549732539343734e+00
      c5 =  4.374664141464968e+00
      c6 =  2.938163982698783e+00

      d1 =  7.784695709041462e-03
      d2 =  3.224671290700398e-01
      d3 =  2.445134137142996e+00
      d4 =  3.754408661907416e+00

      q = sqrt(-2*log(p))

      in (((((c1*q+c2)*q+c3)*q+c4)*q+c5)*q+c6) /
         ((((d1*q+d2)*q+d3)*q+d4)*q+1)

    %inline
    middling : (p : Double) -> Double
    middling p = let
      a1 = -3.969683028665376e+01
      a2 =  2.209460984245205e+02
      a3 = -2.759285104469687e+02
      a4 =  1.383577518672690e+02
      a5 = -3.066479806614716e+01
      a6 =  2.506628277459239e+00

      b1 = -5.447609879822406e+01
      b2 =  1.615858368580409e+02
      b3 = -1.556989798598866e+02
      b4 =  6.680131188771972e+01
      b5 = -1.328068155288572e+01

      q = p - 0.5
      r = q*q

      in (((((a1*r+a2)*r+a3)*r+a4)*r+a5)*r+a6)*q /
         (((((b1*r+b2)*r+b3)*r+b4)*r+b5)*r+1)

export
invnormcdf : Probability -> Double
invnormcdf p =
  if      p == 0 then -1/0
  else if p == 1 then 1/0
  else let
    -- Do one iteration with Halley's root finder to get a more accurate result.
        x = inorm p
        e = (normcdf x).asDouble - p.asDouble
        u = e * sqrt (2*pi) * exp (x*x / 2)
    in x - u / (1 + x * u / 2)

--export
--inverfc : Double -> Double
--inverfc p = - invnormcdf (p/2) / sqrt 2
--
--export
--inverf : Double -> Double
--inverf p = inverfc (1 - p)
