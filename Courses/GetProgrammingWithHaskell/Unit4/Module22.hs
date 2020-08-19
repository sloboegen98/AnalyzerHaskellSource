import System.Environment
import Control.Monad

-- main :: IO ()
-- main = do
--     args <- getArgs
--     let linesToRead = if length args > 0
--                       then read (head args)
--                       else 0 :: Int

--     numbers <- replicateM linesToRead getLine
--     let ints = map read numbers :: [Int]
--     print (sum ints)

toInts :: String -> [Int]
toInts = map read . lines

main :: IO ()
main = do
    userInput <- getContents
    let numbers = toInts userInput
    print (sum numbers)