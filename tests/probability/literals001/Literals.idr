module Literals

import Statistics.Probability

one_fifth : Probability
one_fifth = 1/5

fifty_percent : Probability
fifty_percent = 50.percent

fifty_per_hundred : Probability
fifty_per_hundred = 50/100

fifty_per_hundred' : Probability
fifty_per_hundred' = 50.0/100

fifty_per_hundred'' : Probability
fifty_per_hundred'' = 50/100.0

fifty_per_hundred''' : Probability
fifty_per_hundred''' = 50.0/100.0

full : Probability
full = 1

none : Probability
none = 0

half : Probability
half = 0.5

some : Probability
some = 0.5/8

two_thirds : Probability
two_thirds = 2/3

failing

  x : Probability
  x = 0.5/0.8

failing

  x : Probability
  x = 0.5/0.4

failing

  x : Probability
  x = 500.0/100

failing

  x : Probability
  x = 500/100
