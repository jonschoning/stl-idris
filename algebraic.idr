module algebraic

-- Algebraic laws
-- Motivation: correctness

data Bit = O | I

or : Bit -> Bit -> Bit
or O x1 = x1
or I x1 = I

-- (a `or` b) `or` c = a `or` (b `or` c)

orAssociative : (a : Bit) ->
                (b : Bit) ->
                (c : Bit) ->
                (a `or` b) `or` c = a `or` (b `or` c)
orAssociative O b c = Refl
orAssociative I b c = Refl

BitString : Type
BitString = List Bit

bsor : BitString -> BitString -> BitString
bsor [] x1 = x1
bsor xs [] = xs
bsor (x :: xs) (y :: ys) = (x `or` y) :: (xs `bsor` ys)

bsorAssociative : (a : BitString) ->
                  (b : BitString) ->
                  (c : BitString) ->
                  (a `bsor` b) `bsor` c = a `bsor` (b `bsor` c)
bsorAssociative [] b c = Refl
bsorAssociative (x :: xs) [] c = Refl
bsorAssociative (x :: xs) (y :: ys) [] = Refl
bsorAssociative (x :: xs) (y :: ys) (z :: zs) = 
  rewrite orAssociative x y z in
  rewrite bsorAssociative xs ys zs in
  Refl
