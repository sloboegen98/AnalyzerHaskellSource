{- 
    List of syntatic extension
    https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#syntactic-extensions
-}

{-
    UnboxedTuples
    (# e_1, ..., e_n #)

    f x y = (# x+1, y-1 #)
    g x = case f x x of { (# a, b #) -> a + b }
-}

{-
    UnboxedSums

    (# t_1 | t_2 | ... | t_N #)  
-}

----------------------------------------------------------------------------

-- 1. UnicodeSyntax


{-
    2. MagicHash
    data Person# = Person# { name# :: String, age# :: Natural }
-}

{-
    3. NegativeLiterals
    ???
-}

{-
    4. NumDecimals
    1.2e6 :: Num a => a
-}

{-
    5. BinaryLiterals
    ???
-}

{-
    6. HexFloatLiterals
    ???
-}

{-
    7. NumericUnderscores
    https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#numeric-underscores
-}

{-
    8. PatternGuard
    ???
-}

{-
    9. ViewPatterns

 LANGUAGE ViewPatterns

data JList a = Empty 
                | Single a
                | Join (JList a) (JList a)
 
data JListView a = Nil | Cons a (JList a)

view :: JList a -> JListView a
view Empty = Nil
view (Single a) = Cons a Empty
view (Join (view -> Cons xh xt) y) = Cons xh $ Join xt y
view (Join (view -> Nil) y) = view y

-}

{-
    10. n+k patterns
    ???
-}

{-
    11. RecursiceDo
    LANGUAGE RecursiveDo

justOnes = do { rec { xs <- Just (1:xs) }
              ; return (map negate xs) }

    new keyword 'rec'???
-}

{-
    12. ApplicativeDo
    \m -> do { x <- m; return (not x) }
-}

{-
    13, 14. ParallelListComp + TransformListComp

    [(x, y) | x <- xs | y <- ys]
-}

{-
    15. MonadComperhensions 

    * [ x + y | x <- Just 1, y <- Just 2 ]

    * do x <- Just 1
         y <- Just 2
         return (x+y)

    * [ x | x <- [1..10], x <= 5 ]
-}

{-
    16. MonadFailDesugaring
    ???
-}

{-
    17. NoImplicitPrelude -> RebindableSyntax
    ???

newtype Text = Text String

fromString :: String -> Text
fromString = Text

data Foo = Foo deriving Show
-}

{-
    18. PostfixOperator
    
    (e !)    
-}

{-
    19. TupleSections

    (, True)  
-}

{-
    20. LambdaCase

\case
  p1 -> e1
  ...
  pN -> eN
-}

{-
    21. EmptyCase

case e of { }

data Void
f :: Void -> Int
f x = case x of { }
-}

{-
    22. MultiWayIf

if | guard1 -> expr1
   | ...
   | guardN -> exprN

if | guard1 -> if | guard2 -> expr2
                  | guard3 -> expr3
   | guard4 -> expr4
-}

{-
    23. Local Fixity Declarations
    Deprecated?
-}

{-
    24.1. PackageImports

import "network" Network.Socket

You probably don’t need to use this feature, 
it was added mainly so that we can build
backwards-compatible versions of packages
when APIs change. It can lead to fragile 
dependencies in the common case: modules 
occasionally move from one package to another,
rendering any package-qualified imports broken
-}

{-
    24.2. Safe, Unsafe, Trustworthy

import safe qualified Network.Socket as NS
-}

{-
    24.3. ExplicitNamespaces

module M( f, type (++) ) where ...
  import N( f, type (++) )
  ...
module N( f, type (++) ) where
  data family a ++ b = L a | R b
-}

{-
    25. BlockArguments
Allow do expressions, lambda expressions, etc.
to be directly used as a function argument.

when (x > 0) do
  print x
  exitFailure

withForeignPtr fptr \ptr -> c_memcpy buf ptr size

Changes to the grammars!!!
https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#changes-to-the-grammar
-}

{-
    new keywords

    * forall
    * mdo
    * foreign ?
    * rec, proc, -<, >-, -<<, >>-, (|, |)

    * pattern
    * static
-}

{-
    10.28. Arrows

cmd   ::= exp10 -<  exp
       |  exp10 -<< exp
       |  cmd0
-}

{-
    10.29. BangPatterns

let !x = e in body
let !(p,q) = e in body    
f2 (!x, y) = [x,y]
g7 x = case f x of { !y -> body }
-}

{-
    CPP
    ???
-}

{-
    10.5.2 DisambiguateRecordFields

module M where
  data S = MkS { x :: Int, y :: Bool }

module Foo where
  import M

  data T = MkT { x :: Int }

  ok1 (MkS { x = n }) = n+1   -- Unambiguous
  ok2 n = MkT { x = n+1 }     -- Unambiguous

  bad1 k = k { x = 3 }        -- Ambiguous
  bad2 k = x k                -- Ambiguous


module Foo where
  import M
  x=True
  ok3 (MkS { x }) = x+1   -- Uses both disambiguation and punning
-}

{-
    10.5.3. DuplicateRecordFields

module M where
  data S = MkS { x :: Int }
  data T = MkT { x :: Bool }
-}

{-
    ForignFunctionInterface
    ???
-}

{-
    GADT

Lit    :: Int -> Term Int
Succ   :: Term Int -> Term Int
IsZero :: Term Int -> Term Bool
If     :: Term Bool -> Term a -> Term a -> Term a
Pair   :: Term a -> Term b -> Term (a,b)   
-}

{-
    NamedFieldPuns

data C = C {a :: Int}
f (C {a = a}) = a

-}

{-
    OverloadedLabels

    #foo   
-}

{-
    OverloadedLists

turn off:
[]          -- Empty list
[x]         -- x : []
[x,y,z]     -- x : y : z : []
[x .. ]     -- enumFrom x
[x,y ..]    -- enumFromThen x y
[x .. y]    -- enumFromTo x y
[x,y .. z]  -- enumFromThenTo x y z

turn on:
[]          -- fromListN 0 []
[x]         -- fromListN 1 (x : [])
[x,y,z]     -- fromListN 3 (x : y : z : [])
[x .. ]     -- fromList (enumFrom x)
[x,y ..]    -- fromList (enumFromThen x y)
[x .. y]    -- fromList (enumFromTo x y)
[x,y .. z]  -- fromList (enumFromThenTo x y z)

['0' .. '9']             :: Set Char
[1 .. 10]                :: Vector Int
[("default",0), (k1,v1)] :: Map String Int
['a' .. 'z']             :: Text

syntactic???
-}

{-
    OverloadedStrings

    ???
-}

{-
    PatternGuards, maybe NoPatternGuards
    ?? in standard grammar ??
-}