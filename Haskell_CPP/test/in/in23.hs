divideByFirstElem (x:xs) = help x [[],[],[]] (x:xs)
    where
        help x acc [] = acc
        help x (eq:less:more:t) (y:ys)
            | y == x = help x ((eq ++ [y]):less:more:t) ys
            | y < x = help x (eq:(less ++ [y]):more:t) ys
            | otherwise = help x (eq:less:(more ++ [y]):t) ys


repl :: Int -> a -> [a]
repl 0 _ = []
repl n a 
        |n<0 = error "n<0"
        |otherwise = a : repl (n-1) a