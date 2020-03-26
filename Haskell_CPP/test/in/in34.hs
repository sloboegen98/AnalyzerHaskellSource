{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

intAdd :: Num Int => Int -> Int -> Int 
intAdd = (+)

class Shower a b where
  myShow :: a -> b

doSomething :: Shower a String => a -> String
doSomething = myShow