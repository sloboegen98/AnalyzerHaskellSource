main = do
    [fname,l] <- getArgs
    file <- readFile fname
    let len = read l :: Int
    putStr . show $ report len (getWords file)