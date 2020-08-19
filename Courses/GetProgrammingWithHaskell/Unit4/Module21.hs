fib :: Integer -> Integer

fib n = helper n 0 1 where
    helper 0 curr prev  = curr
    helper n' curr prev = helper (n' - 1) (curr + prev) curr


main :: IO ()
main = do
    num <- getLine
    let res = fib (read num)
    putStrLn (show res)