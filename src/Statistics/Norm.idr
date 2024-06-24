||| Stuff related to the normal distribution
module Statistics.Norm

import public Statistics.Probability

%default total

||| Cumulative distribution function (CDF) of the normal distribution
public export
interface NormCDF where
  normcdf : SolidDouble -> Probability

||| Inverse cumulative distribution function of the normal distribution
public export
interface InvNormCDF where
  invnormcdf : Probability -> SolidDouble
