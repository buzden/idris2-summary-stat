module Statistics.Erf

import public Statistics.Norm
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

export
inverfc : InvNormCDF => DoubleBetween 0 2 -> SolidDouble
inverfc p = - invnormcdf (P $ p/2) / sqrt 2

export
inverf : InvNormCDF => DoubleBetween (-1) 1 -> SolidDouble
inverf p = inverfc (1 - p)
