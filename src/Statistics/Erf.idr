module Statistics.Erf

import public Statistics.Probability

%default total

--- Error function and co ---

%foreign "C:erfc, libm 6"
prim_erfc : Double -> Double

export
erfc : SolidDouble -> DoubleBetween 0 2
erfc = roughlyFit . prim_erfc . cast

export
erf : SolidDouble -> DoubleBetween (-1) 1
erf x = 1 - erfc x

-- Code below is based on taken from
-- https://hackage.haskell.org/package/erf-2.0.0.0/docs/src/Data-Number-Erf.html
-- Licensed with BSD-3-Clause, copyright Lennart Augustsson

export
normcdf : SolidDouble -> Probability
normcdf x = P $ erfc (-x / sqrt 2) / 2

-- calculation with precision only up to 10^9
-- this implementation does not require error function implementation (which now is implemented through a `%foreign` function)
export
invnormcdf' : Probability -> SolidDouble
invnormcdf' p =
    let res = if      p == 0       then NegInf
              else if p == 1       then PosInf
              else if p < pLow     then closeToLowBound p
              else if p.inv < pLow then - closeToLowBound p.inv
              else                      middling p
    in roughlyFit res

  where
    pLow : Probability
    pLow = 0.02425

    closeToLowBound : Probability -> Double
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

      q = sqrt(-2*log(p.asDouble))

      in (((((c1*q+c2)*q+c3)*q+c4)*q+c5)*q+c6) /
         ((((d1*q+d2)*q+d3)*q+d4)*q+1)

    %inline
    middling : Probability -> Double
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

      q = p.asDouble - 0.5
      r = q*q

      in (((((a1*r+a2)*r+a3)*r+a4)*r+a5)*r+a6)*q /
         (((((b1*r+b2)*r+b3)*r+b4)*r+b5)*r+1)

export
invnormcdf : Probability -> SolidDouble
invnormcdf p =
  if      p == 0 then NegInf
  else if p == 1 then PosInf
  else let -- Do one iteration with Halley's root finder to get a more accurate result.
    x = invnormcdf' p
    e = (normcdf x).asDouble - p.asDouble
    x = x.asDouble
    u = e * sqrt (2*pi) * exp (x*x / 2)
    x' = x - u / (1 + x * u / 2)
    in roughlyFit x'

export
inverfc : DoubleBetween 0 2 -> SolidDouble
inverfc p = - invnormcdf (P $ p/2) / sqrt 2

export
inverf : DoubleBetween (-1) 1 -> SolidDouble
inverf p = inverfc (1 - p)
