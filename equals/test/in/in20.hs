doGuessing num = do
    putStrLn "Enter your guess:"
    guess <- getLine
    case compare (read guess) num of
      EQ -> do putStrLn "You win!"
               return ()