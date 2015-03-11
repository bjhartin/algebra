-- Thanks to http://www.staff.science.uu.nl/~fokke101/article/algebra/algebra.pdf.
module Main where

class Eq a => Monoid a where
    (<+>) :: a -> a -> a -- (closure, in the mathematical sense)
    zzero :: a

{-
 Monoid laws:
   x <+> (y <+> z) == (x <+> y) <+> z (associativity)
   zzero <+> y == y (identity element)
   z <+> zzero == z (identity element - expressed twice because general commutativity is __not__ required for <+>)
-}

class Monoid a => Group a where
    neg :: a -> a

{-
 Group law: For any a, there exists b such that a <+> b == zzero (we express b as 'neg a' below)
   x <+> neg x == zzero
   neg x <+> x == zzero
-}

{- Abelian (commutative) group law:
  x <+> y == y <+> x
-}

class Group a => Ring a where
    (<*>) :: a -> a -> a
    one :: a

{-
  Ring laws: Adds an associative 'multiply' operator which distributes over addition and has identity element
    x <*> (y <*> z) == (x <*> y) <*> z (associativity)
    x <*> (<y> <+> <z>) == x <*> y <+> x <*> z (distributivity)
    (x <+> y) <*> z == x <*> z <+> y <*> z (expressed twice because general commutativity is __not__ required for <*>)
    one <*> x == x (identity element)
    x <*> one == x (identity element - expressed twice because general commutativity is __not__ required for <*>)
-}

{-
  NOTE: Original author's text has a 'Rng' type, identical to Ring save lacking an identity element.
  I may need to resurrect that, but have left it out for now.
-}

class Ring a => Euclid a where
  degree :: a->Int
  divide :: a->a->a
  modulo :: a->a->a
  x `modulo` y | y/=zzero = x <+> neg((x `divide` y) <*> y)

-- y/=zzero | degree (x ‘modulo‘ y) < degree y
-- || x ‘modulo‘ y == zzero
-- y/=zzero | degree x <= degree (x<*>y)

{-
  Euclidean space laws: Adds a 'divide' operator which produces a quotient and remainder
-}

class Ring a => Field a where
  inv :: a -> a

{-

  Field law: x/=zzero | x <*> inv x == one

-}


-- | The main entry point.
main :: IO ()
main = do
    putStrLn "Welcome to FP Haskell Center!"
    putStrLn "Have a good day!"
