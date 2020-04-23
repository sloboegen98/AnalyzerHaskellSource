{-# LANGUAGE RecursiveDo #-}
import Data.IORef
data Node = Node Int (IORef Node)

mknode = do
    rec p <- newIORef (Node 0 p)
    putStrLn "node created"
    return p

main = do
  p <- mknode
  Node x q <- readIORef p
  print x
  Node y _ <- readIORef q
  print y