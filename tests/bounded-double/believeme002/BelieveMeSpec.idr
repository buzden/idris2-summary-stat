module BelieveMeSpec

import Data.Double.Bounded

import Hedgehog

import Test.Common

sp : (l ** u ** DoubleBetween l u)
sp = (_ ** _ ** 1)

plus_corr : Property
plus_corr = property $ do
  (((l ** u ** x), (l' ** u' ** x')) ** (f1, f2)) <-
    forAllDefault ((sp, sp) ** %search) $ [| (someBoundedDouble, someBoundedDouble) |] `plus` \x => do
      let l = fst $ fst x
      let u = fst $ snd $ fst x
      let l' = fst $ snd x
      let u' = fst $ snd $ snd x
      ( Finite l `OR` Finite l' `OR` So (l == l')
      , Finite u `OR` Finite u' `OR` So (u == u')
        )
  boundedDoubleCorrect $ (x + x') @{f1} @{f2}

minus_corr : Property
minus_corr = property $ do
  (((l ** u ** x), (l' ** u' ** x')) ** (f1, f2)) <-
    forAllDefault ((sp, sp) ** %search) $ [| (someBoundedDouble, someBoundedDouble) |] `plus` \x => do
      let l = fst $ fst x
      let u = fst $ snd $ fst x
      let l' = fst $ snd x
      let u' = fst $ snd $ snd x
      ( Finite l `OR` Finite u' `OR` So (l /= u')
      , Finite u `OR` Finite l' `OR` So (u /= l')
        )
  boundedDoubleCorrect $ (x - x') @{f1} @{f2}

mul_corr : Property
mul_corr = property $ do
  (((l ** u ** x), (l' ** u' ** x')) ** (f1, f2, f3, f4, f5, f6, f7, f8)) <-
    forAllDefault ((sp, sp) ** %search) $ [| (someBoundedDouble, someBoundedDouble) |] `plus` \x => do
      let l = fst $ fst x
      let u = fst $ snd $ fst x
      let l' = fst $ snd x
      let u' = fst $ snd $ snd x
      ( Finite l `OR` NonZero l'
      , Finite l `OR` NonZero u'
      , Finite u `OR` NonZero l'
      , Finite u `OR` NonZero u'
      , Finite l' `OR` NonZero l
      , Finite l' `OR` NonZero u
      , Finite u' `OR` NonZero l
      , Finite u' `OR` NonZero u
        )
  boundedDoubleCorrect $ (x * x') @{f1} @{f2} @{f3} @{f4} @{f5} @{f6} @{f7} @{f8}

div_corr : Property
div_corr = property $ do
  (((l ** u ** x), (l' ** u' ** x')) ** (f1, f2, f3, f4, f5, f6, f7, f8, f9, f10)) <-
    forAllDefault ((sp, sp) ** %search) $ [| (someBoundedDouble, someBoundedDouble) |] `plus` \x => do
      let l = fst $ fst x
      let u = fst $ snd $ fst x
      let l' = fst $ snd x
      let u' = fst $ snd $ snd x
      let num = snd $ snd $ fst x
      let den = snd $ snd $ snd x
      ( So (0 < l') `OR` So (u' < 0) `OR` So (l' < 0 && 0 < u' && l /= 0 && u /= 0)
      , So (0 < l) `OR` So (u < 0) `OR` So (0 < l') `OR` So (u' < 0) `OR` (NonZero num.asDouble, NonZero den.asDouble)
      , Finite l `OR` Finite l'
      , Finite l `OR` Finite u'
      , Finite u `OR` Finite l'
      , Finite u `OR` Finite u'
      , NonZero l `OR` NonZero l'
      , NonZero l `OR` NonZero u'
      , NonZero u `OR` NonZero l'
      , NonZero u `OR` NonZero u'
        )
  boundedDoubleCorrect $ (x / x') @{f1} @{f2} @{f3} @{f4} @{f5} @{f6} @{f7} @{f8} @{f9} @{f10}

negate_corr : Property
negate_corr = property $ do
  (_ ** _ ** x) <- forAll someBoundedDouble
  boundedDoubleCorrect $ negate x

main : IO ()
main = test
  [ "believe_me" `MkGroup`
      [ ("(+)", plus_corr)
      , ("(-)", minus_corr)
      , ("(*)", mul_corr)
      , ("(/)", div_corr)
      , ("negate", negate_corr)
      ]
  ]
