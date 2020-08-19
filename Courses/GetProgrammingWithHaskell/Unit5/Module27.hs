data Box a = Box a deriving Show

instance Functor Box where
    fmap f (Box val) = Box (f val)

myBox :: Box Int
myBox = Box 1

morePresents :: Int -> Box a -> Box [a]
morePresents n box = (take n) <$> (fmap repeat box)

unwrap :: Box a -> a
unwrap (Box val) = val
