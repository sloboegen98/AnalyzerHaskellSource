{-# LANGUAGE DerivingVia #-}

newtype Unicode = U Int
  deriving Show
    via (Hex Int)