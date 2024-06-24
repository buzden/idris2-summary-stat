module Statistics.Norm.Precise

import Statistics.Erf
import public Statistics.Norm
import Statistics.Norm.Rough

%default total

export
NormCDF where
  normcdf x = P $ erfc (-x / sqrt 2) / 2

-- theoretically, it can get rough `InvNormCDF` as an auto-implicit, i.e. to improve any implementation
export
InvNormCDF where
  -- Code below is based on taken from
  -- https://hackage.haskell.org/package/erf-2.0.0.0/docs/src/Data-Number-Erf.html
  -- Licensed with BSD-3-Clause, copyright Lennart Augustsson
  invnormcdf p =
    if      p == 0 then NegInf
    else if p == 1 then PosInf
    else let -- Do one iteration with Halley's root finder to get a more accurate result.
      x = invnormcdf @{Rough} p
      e = (normcdf x).asDouble - p.asDouble
      x = x.asDouble
      u = e * sqrt (2*pi) * exp (x*x / 2)
      x' = x - u / (1 + x * u / 2)
      in roughlyFit x'
