{-# LANGUAGE RecursiveDo #-}
import Data.IORef
data Node = Node Int (IORef Node)
mk2nodes = mdo
  p <- newIORef (Node 0 r)
  r <- newIORef (Node 1 p)
  putStrLn "nodes created"
  return p

main = do
  p <- mk2nodes
  Node x q <- readIORef p
  print x
  Node y _ <- readIORef q
  print y